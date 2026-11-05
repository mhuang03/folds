//! Block-streamed meet in the middle: the same DP as `dp.rs`, but layers are freed
//! block by block, and the last layer is never stored whole.
//!
//! A layer lives in one `mmap`ed region with `MAP_NORESERVE`, so only the pages that
//! are written count toward memory.  The blocks `(i, j, c)` of layer `k` are computed
//! one at a time.  Output block `(i, j, c)` pulls only from blocks of layer `k-1`
//! whose `L`-size is `i-1` or `i`:
//!   * `(i-1, j, c)` (remove a left panel),
//!   * `(i, j-1, c)` (remove a right panel; for `j = i` this is the mirror of `(i-1, i, c)`),
//!   * `(i, j, 0)`   (remove the middle panel, odd `N` and `c = 1`).
//!
//! So the blocks are computed in order of `i` (increasing or decreasing, whichever
//! gives the smaller simulated peak), and each block of layer `k-1` is released
//! (`MADV_DONTNEED` + `PROT_NONE`, so a stray read would fault) right after the last
//! output block that needs it.
//!
//! The final step is streamed:
//!   * even `N = 2k`: complementing maps block `(i, k-i)` of layer `k` to itself
//!     (`|~L| = h-i = k-i`), so each block of the middle layer is computed, combined
//!     with itself (`Σ g(S) g(S^c)`) and dropped at once;
//!   * odd `N = 2k+1` (fused form `Σ_{|U|=k+1} g(U) g(U^c)`): the complement of block
//!     `(i, j, c)` of layer `k+1` is block `(i+c-1, h-i, 1-c)` of layer `k`, whose
//!     `L`-size is again `i-1` or `i`.  So the same order works, layer `k+1` is only
//!     ever held as a tile of 16 rows, and layer `k` is released as it is consumed.
//!
//! Peak memory is therefore (for each step) the simulated maximum of
//! "live blocks of layer `k-1`" + "blocks of layer `k` written so far", instead of
//! two full layers.

use crate::dp::{weight, Ring, Word};
use crate::layout::{entry, Block, Layout, Shape};
use rayon::prelude::*;
use std::time::Instant;

unsafe extern "C" {
    fn mmap(addr: *mut std::ffi::c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut std::ffi::c_void;
    fn munmap(addr: *mut std::ffi::c_void, len: usize) -> i32;
    fn madvise(addr: *mut std::ffi::c_void, len: usize, advice: i32) -> i32;
    fn mprotect(addr: *mut std::ffi::c_void, len: usize, prot: i32) -> i32;
    fn fallocate(fd: i32, mode: i32, off: i64, len: i64) -> i32;
    fn sync_file_range(fd: i32, off: i64, len: i64, flags: u32) -> i32;
}
const MAP_SHARED: i32 = 0x01;
const FALLOC_FL_KEEP_SIZE: i32 = 0x01;
const FALLOC_FL_PUNCH_HOLE: i32 = 0x02;
const PROT_NONE: i32 = 0;
const PROT_RW: i32 = 3;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const MAP_NORESERVE: i32 = 0x4000;
const MADV_DONTNEED: i32 = 4;
const MADV_HUGEPAGE: i32 = 14;
const MADV_WILLNEED: i32 = 3;
const PAGE: usize = 4096;

/// A lazily backed array of `len` words, zero on first touch.  Anonymous `mmap` by
/// default.  With `FOLDS_SPILL=<dir>`, regions of at least `FOLDS_SPILL_MIN` bytes
/// (default 1e9) are `MAP_SHARED` mappings of a sparse file in `<dir>` instead: the
/// pages are then page cache, which the kernel can write back and evict under memory
/// pressure instead of OOM-killing (this VM puts all tool processes in one 14.3 GB
/// memory cgroup).  Released ranges are hole-punched, so disk use follows the live set.
pub struct Region<W: Word> {
    ptr: *mut W,
    len: usize,
    bytes: usize,
    file: Option<(std::fs::File, std::path::PathBuf)>,
}
unsafe impl<W: Word> Send for Region<W> {}
unsafe impl<W: Word> Sync for Region<W> {}

pub fn spill_dir(bytes: usize) -> Option<std::path::PathBuf> {
    let dir = std::env::var_os("FOLDS_SPILL")?;
    let min: usize = std::env::var("FOLDS_SPILL_MIN").ok().and_then(|v| v.parse().ok()).unwrap_or(1_000_000_000);
    (bytes >= min).then(|| std::path::PathBuf::from(dir))
}

impl<W: Word> Region<W> {
    pub fn new(len: usize) -> Self {
        let bytes = (len.max(1) * W::BYTES + PAGE - 1) / PAGE * PAGE;
        let dir = spill_dir(bytes);
        Self::with(len, dir.as_deref(), true)
    }
    /// A region backed by a sparse file in `dir` (`Some`) or anonymous memory
    /// (`None`; with `huge`, transparent huge pages are requested).
    pub fn with(len: usize, dir: Option<&std::path::Path>, huge: bool) -> Self {
        use std::os::unix::io::AsRawFd;
        static SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let bytes = (len.max(1) * W::BYTES + PAGE - 1) / PAGE * PAGE;
        if let Some(dir) = dir {
            let path = dir.join(format!(
                "folds-{}-{}.bin",
                std::process::id(),
                SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            ));
            let f = std::fs::OpenOptions::new().read(true).write(true).create_new(true).open(&path).expect("spill file");
            f.set_len(bytes as u64).expect("spill set_len");
            let p = unsafe { mmap(std::ptr::null_mut(), bytes, PROT_RW, MAP_SHARED, f.as_raw_fd(), 0) };
            assert!(p as isize != -1, "mmap of spill file {path:?} failed");
            return Region { ptr: p as *mut W, len, bytes, file: Some((f, path)) };
        }
        let p = unsafe {
            mmap(std::ptr::null_mut(), bytes, PROT_RW, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0)
        };
        assert!(p as isize != -1, "mmap of {bytes} bytes failed");
        if huge && bytes >= 1 << 22 {
            unsafe { madvise(p, bytes, MADV_HUGEPAGE) };
        }
        Region { ptr: p as *mut W, len, bytes, file: None }
    }
    pub fn ptr(&self) -> *mut W {
        self.ptr
    }
    pub fn is_file(&self) -> bool {
        self.file.is_some()
    }
    /// File-backed only: start writeback of `[start, start+len)` (asynchronously).
    pub fn flush_async(&self, start: usize, len: usize) {
        use std::os::unix::io::AsRawFd;
        if let Some((f, _)) = &self.file {
            unsafe { sync_file_range(f.as_raw_fd(), (start * W::BYTES) as i64, (len * W::BYTES) as i64, 2) };
        }
    }
    /// File-backed only: ask the kernel to read `[start, start+len)` ahead.
    pub fn prefetch(&self, start: usize, len: usize) {
        if self.file.is_some() {
            let a = (self.ptr as usize + start * W::BYTES) / PAGE * PAGE;
            let b = self.ptr as usize + (start + len) * W::BYTES;
            if b > a {
                unsafe { madvise(a as *mut _, b - a, MADV_WILLNEED) };
            }
        }
    }
    #[inline(always)]
    pub fn data(&self) -> &[W] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
    /// Mutable view of `[start, start+len)`.  Callers hand out disjoint ranges only.
    #[allow(clippy::mut_from_ref)]
    #[inline(always)]
    pub unsafe fn part(&self, start: usize, len: usize) -> &mut [W] {
        debug_assert!(start + len <= self.len);
        unsafe { std::slice::from_raw_parts_mut(self.ptr.add(start), len) }
    }
    /// Give the pages lying entirely inside `[start, start+len)` back to the OS and
    /// make them inaccessible.
    pub fn release(&self, start: usize, len: usize) {
        use std::os::unix::io::AsRawFd;
        let a = (self.ptr as usize + start * W::BYTES + PAGE - 1) / PAGE * PAGE;
        let b = (self.ptr as usize + (start + len) * W::BYTES) / PAGE * PAGE;
        if b > a {
            unsafe {
                madvise(a as *mut _, b - a, MADV_DONTNEED);
                mprotect(a as *mut _, b - a, PROT_NONE);
                if let Some((f, _)) = &self.file {
                    let off = (a - self.ptr as usize) as i64;
                    fallocate(f.as_raw_fd(), FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE, off, (b - a) as i64);
                }
            }
        }
    }
}
impl<W: Word> Drop for Region<W> {
    fn drop(&mut self) {
        unsafe { munmap(self.ptr as *mut _, self.bytes) };
        if let Some((_, path)) = &self.file {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// Canonical block index of `(i, j, c)` in `sh` (mirror applied), if it exists.
fn find(sh: &Shape, i: isize, j: isize, c: usize) -> Option<usize> {
    if i < 0 || j < 0 {
        return None;
    }
    let (a, b) = if i <= j { (i as usize, j as usize) } else { (j as usize, i as usize) };
    sh.blocks.iter().position(|bl| bl.i == a && bl.j == b && bl.c == c)
}

/// Blocks of `prev` (layer `k-1`) read by the pull into block `bl` of layer `k`.
fn pull_needs(prev: &Shape, bl: &Block) -> Vec<usize> {
    let (i, j) = (bl.i as isize, bl.j as isize);
    let mut v = vec![];
    v.extend(find(prev, i - 1, j, bl.c));
    v.extend(find(prev, i, j - 1, bl.c));
    if bl.c == 1 {
        v.extend(find(prev, i, j, 0));
    }
    v.sort();
    v.dedup();
    v
}

/// Order the output blocks by `i` (then `c`), increasing or decreasing, and return
/// the order, the step after which each prev block can be freed, and the simulated
/// peak (in words).  `out_mode`: 2 = output blocks stay resident after their step,
/// 1 = only the current output block is resident, 0 = output is never stored.
fn schedule(prev: &Shape, out: &Shape, needs: &[Vec<usize>], out_mode: u8) -> (Vec<usize>, Vec<usize>, usize) {
    let eval = |order: &[usize]| -> (Vec<usize>, usize) {
        let mut last = vec![usize::MAX; prev.blocks.len()];
        for (t, &b) in order.iter().enumerate() {
            for &p in &needs[b] {
                last[p] = t;
            }
        }
        // prev blocks never needed are freed before step 0 (never happens in practice)
        let mut live: usize = prev.blocks.iter().enumerate().filter(|(p, _)| last[*p] != usize::MAX).map(|(_, b)| b.len).sum();
        let mut outsum = 0usize;
        let mut peak = 0usize;
        for (t, &b) in order.iter().enumerate() {
            let cur = if out_mode >= 1 { out.blocks[b].len } else { 0 };
            peak = peak.max(live + outsum + cur);
            if out_mode == 2 {
                outsum += cur;
            }
            for &p in &needs[b] {
                if last[p] == t {
                    live -= prev.blocks[p].len;
                    last[p] = usize::MAX - 1; // freed once
                }
            }
        }
        (last, peak)
    };
    let mut best: Option<(Vec<usize>, usize)> = None;
    for dec in [false, true] {
        let mut order: Vec<usize> = (0..out.blocks.len()).collect();
        order.sort_by_key(|&b| (out.blocks[b].i, out.blocks[b].c));
        if dec {
            order.reverse();
        }
        let (_, peak) = eval(&order);
        if best.as_ref().is_none_or(|x| peak < x.1) {
            best = Some((order, peak));
        }
    }
    // Any order is correct (a prev block is freed after its last reader), so improve
    // the peak by a deterministic local search over insertion moves.
    let (mut order, mut peak) = best.unwrap();
    let nb = order.len();
    if nb > 2 && out_mode == 2 {
        let mut x = 0x9E3779B97F4A7C15u64;
        let mut rnd = |m: usize| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x % m as u64) as usize
        };
        for _ in 0..100_000 {
            let (a, b) = (rnd(nb), rnd(nb));
            let mut o = order.clone();
            let v = o.remove(a);
            o.insert(b, v);
            let (_, p) = eval(&o);
            if p <= peak {
                order = o;
                peak = p;
            }
        }
    }
    let mut last = vec![usize::MAX; prev.blocks.len()];
    for (t, &b) in order.iter().enumerate() {
        for &p in &needs[b] {
            last[p] = t;
        }
    }
    (order, last, peak)
}

/// Rows of block `bl`: `(row, start, len)`.
fn block_rows(lay: &Layout, bl: &Block) -> Vec<(usize, usize, usize)> {
    let h = lay.h;
    let ci = lay.binom[h][bl.i] as usize;
    if bl.i < bl.j {
        let cj = lay.binom[h][bl.j] as usize;
        (0..ci).map(|r| (r, bl.off + r * cj, cj)).collect()
    } else {
        (0..ci).map(|r| (r, bl.off + r * (r + 1) / 2, r + 1)).collect()
    }
}

/// Rows per tile of the diagonal kernel.
const DT: usize = 64;

/// Tile `[r0, r1)` of rows of a diagonal block `(i, i, c)` (row `ρ` = rank R, column
/// = rank L `≤ ρ`), written to `out` = the contiguous triangle rows `r0..r1`.
///
/// The row-by-row kernel (`generic_row`) reads `g(L\x, R)` at row `rank(L\x)`,
/// column `ρ` of block `(i-1, i, c)`: one cache miss per read.  Walking the tile
/// column by column instead, those reads for the `DT` rows of the tile are `DT`
/// consecutive words, while the reads `g(L, R\y)` (row `rank(R\y)`, column
/// `rank L`) and the middle-panel reads stay sequential per row.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn diag_tile<W: Word>(lay: &Layout, chk: &crate::rule::Checker, ring: Ring, ps: &Shape, pd: &[W], bl: &Block, r0: usize, r1: usize, out: &mut [W]) {
    let (i, c, h) = (bl.i, bl.c, lay.h);
    debug_assert_eq!(bl.i, bl.j);
    let base = r0 * (r0 + 1) / 2;
    let un = &lay.un[i];
    // block (i-1, i, c): both L- and R-removals land there
    let a = if i > 0 { Some(ps.slot[2 * (i - 1) + c]) } else { None };
    let (aoff, alen) = a.map(|s| (s.off, s.rowlen)).unwrap_or((0, 0));
    let moff = if c == 1 { ps.slot[2 * i].off } else { 0 };
    let rshift = lay.n - 1;
    // per row of the tile: (panel, prev row start) for each y in R
    let mut ry: Vec<[(u32, usize); 32]> = Vec::with_capacity(r1 - r0);
    for rho in r0..r1 {
        let r = un[rho];
        let mut v = [(0u32, 0usize); 32];
        let mut bits = r;
        let mut q = 0;
        while bits != 0 {
            let y = bits.trailing_zeros();
            bits &= bits - 1;
            v[q] = ((rshift - y as usize) as u32, aoff + lay.rank[(r ^ (1 << y)) as usize] as usize * alen);
            q += 1;
        }
        ry.push(v);
    }
    let mut lx = [(0u32, 0usize); 32];
    for col in 0..r1 {
        let l = un[col];
        let mut nl = 0;
        let mut bits = l;
        while bits != 0 {
            let x = bits.trailing_zeros();
            bits &= bits - 1;
            lx[nl] = (x, aoff + lay.rank[(l ^ (1 << x)) as usize] as usize * alen);
            nl += 1;
        }
        for rho in r0.max(col)..r1 {
            let t = lay.compose_col(l, c, i, rho);
            let mut acc = 0u64;
            for &(x, b) in &lx[..nl] {
                let v = unsafe { pd.get_unchecked(b + rho).get64() };
                acc += v & mask(chk.valid(t ^ (1u64 << x), x));
            }
            for &(p, b) in &ry[rho - r0][..i] {
                let v = unsafe { pd.get_unchecked(b + col).get64() };
                acc += v & mask(chk.valid(t ^ (1u64 << p), p));
            }
            if c == 1 {
                let v = unsafe { pd.get_unchecked(moff + rho * (rho + 1) / 2 + col).get64() };
                acc += v & mask(chk.valid(t ^ (1u64 << h), h as u32));
            }
            unsafe { *out.get_unchecked_mut(rho * (rho + 1) / 2 + col - base) = W::put(ring.red(acc as u128)) };
        }
    }
}

#[inline(always)]
fn mask(b: bool) -> u64 {
    (b as u64).wrapping_neg()
}

/// Rows per tile of the off-diagonal tile kernel.
const OT: usize = 16;

/// Rows `[r0, r1)` of an off-diagonal block `(i, j, c)`, `i < j`, into `out`
/// (`(r1-r0) × C(h,j)`, row-major).  Same sums as `offdiag_row`, walked column by
/// column over the tile.  This matters for `j = i+1`: removing a right panel then
/// lands in the *diagonal* block `(i, i, c)`, where `g(L, R\y)` with
/// `rank(R\y) > rank L` sits at row `rank(R\y)`, column `rank L` of the triangle;
/// the row kernel takes one cache miss per such read, the tile reads `OT`
/// consecutive words.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn offdiag_tile<W: Word>(lay: &Layout, chk: &crate::rule::Checker, ring: Ring, ps: &Shape, pd: &[W], bl: &Block, r0: usize, r1: usize, out: &mut [W]) {
    let (i, j, c, h) = (bl.i, bl.j, bl.c, lay.h);
    debug_assert!(i < j);
    let nr = r1 - r0;
    let cj = lay.binom[h][j] as usize;
    let un_i = &lay.un[i];
    let un_j = &lay.un[j];
    let rrem = &lay.rrem[j];
    let rshift = lay.n - 1;
    // per tile row: L, its left-removal streams, its middle stream, its R-row base
    let mut ls = [0u32; OT];
    let mut lx = [[(0u32, 0usize); 32]; OT];
    let mut mid = [0usize; OT];
    let mut rb = [0usize; OT];
    let diag_r = i == j - 1;
    let rsl = ps.slot[2 * i + c]; // block (i, j-1, c) (a triangle when j-1 = i)
    for q in 0..nr {
        let row = r0 + q;
        let l = un_i[row];
        ls[q] = l;
        if i > 0 {
            let sl = ps.slot[2 * (i - 1) + c];
            let mut bits = l;
            let mut t = 0;
            while bits != 0 {
                let x = bits.trailing_zeros();
                bits &= bits - 1;
                lx[q][t] = (x, sl.off + lay.rank[(l ^ (1 << x)) as usize] as usize * sl.rowlen);
                t += 1;
            }
        }
        if c == 1 {
            let sl = ps.slot[2 * i];
            mid[q] = sl.off + row * sl.rowlen;
        }
        rb[q] = if diag_r { 0 } else { rsl.off + row * rsl.rowlen };
    }
    let mut ry = [(0u32, 0usize); 32];
    for col in 0..cj {
        let r = un_j[col];
        let mut bits = r;
        let mut t = 0;
        while bits != 0 {
            let y = bits.trailing_zeros();
            bits &= bits - 1;
            ry[t] = ((rshift - y as usize) as u32, unsafe { *rrem.get_unchecked(col * j + t) } as usize);
            t += 1;
        }
        let rv = (unsafe { *lay.revc[j].get_unchecked(col) } as u64) << (lay.n - h);
        for q in 0..nr {
            let t = ls[q] as u64 | (c as u64) << h | rv;
            // branch-free: the validity bits are unpredictable, the loads are cheap
            let mut acc = 0u64;
            for &(x, b) in &lx[q][..i] {
                let v = unsafe { pd.get_unchecked(b + col).get64() };
                acc += v & mask(chk.valid(t ^ (1u64 << x), x));
            }
            if c == 1 {
                let v = unsafe { pd.get_unchecked(mid[q] + col).get64() };
                acc += v & mask(chk.valid(t ^ (1u64 << h), h as u32));
            }
            let row = r0 + q;
            for &(p, rr) in &ry[..j] {
                let ix = if !diag_r {
                    rb[q] + rr
                } else if rr <= row {
                    rsl.off + row * (row + 1) / 2 + rr
                } else {
                    rsl.off + rr * (rr + 1) / 2 + row
                };
                let v = unsafe { pd.get_unchecked(ix).get64() };
                acc += v & mask(chk.valid(t ^ (1u64 << p), p));
            }
            unsafe { *out.get_unchecked_mut(q * cj + col) = W::put(ring.red(acc as u128)) };
        }
    }
}

/// Compute block `bl` of the layer `out_shape` into `out` from the layer `ps`/`pd`.
fn compute_block<W: Word>(lay: &Layout, chk: &crate::rule::Checker, ring: Ring, ps: &Shape, pd: &[W], bl: &Block, out: &Region<W>) {
    if bl.i == bl.j {
        let ci = lay.binom[lay.h][bl.i] as usize;
        let tiles: Vec<usize> = (0..ci).step_by(DT).collect();
        tiles.into_par_iter().for_each(|r0| {
            let r1 = (r0 + DT).min(ci);
            let o = unsafe { out.part(bl.off + r0 * (r0 + 1) / 2, r1 * (r1 + 1) / 2 - r0 * (r0 + 1) / 2) };
            diag_tile(lay, chk, ring, ps, pd, bl, r0, r1, o);
        });
        return;
    }
    let ci = lay.binom[lay.h][bl.i] as usize;
    let cj = lay.binom[lay.h][bl.j] as usize;
    let tr = tile_rows(bl);
    let tiles: Vec<usize> = (0..ci).step_by(tr).collect();
    tiles.into_par_iter().for_each(|r0| {
        let r1 = (r0 + tr).min(ci);
        let o = unsafe { out.part(bl.off + r0 * cj, (r1 - r0) * cj) };
        offdiag_tile(lay, chk, ring, ps, pd, bl, r0, r1, o);
    });
}

/// Tile height for an off-diagonal block: `OT` when right removals hit the diagonal
/// block (see `offdiag_tile`), else a few rows (the tile keeps one row of block
/// `(i, j-1, c)` per tile row in cache).
fn tile_rows(bl: &Block) -> usize {
    if bl.j == bl.i + 1 { OT } else { 4 }
}

#[inline(always)]
fn md(x: u128, ring: Ring) -> u128 {
    ring.red_any(x)
}

/// Even `N`, middle layer: position of the orbit of `S^c` for entry `(row, col)` of
/// block `bl` (same block; complementing reverses colex order, `C = C(h,i) = C(h,j)`).
#[inline(always)]
fn even_comp(bl: &Block, cc: usize, row: usize, col: usize) -> usize {
    if bl.i < bl.j {
        // (rank L, rank R) -> (rank ~R, rank ~L)
        bl.off + (cc - 1 - col) * cc + (cc - 1 - row)
    } else {
        // triangle (row = rank R >= col = rank L) -> max = C-1-col, min = C-1-row
        let m = cc - 1 - col;
        bl.off + m * (m + 1) / 2 + (cc - 1 - row)
    }
}

/// Even `N`: `Σ_{S in block} w(S) g(S) g(S^c)` where `S^c` lies in the same block.
fn even_block_sum<W: Word>(lay: &Layout, ring: Ring, sh: &Shape, d: &[W], bl: &Block) -> u128 {
    let full = lay.full();
    let rows = block_rows(lay, bl);
    const B: usize = 32;
    let bands: Vec<usize> = (0..rows.len()).step_by(B).collect();
    let maxlen = rows.iter().map(|r| r.2).max().unwrap_or(0);
    let cc = lay.binom[lay.h][bl.i] as usize;
    debug_assert_eq!(cc, lay.binom[lay.h][bl.j] as usize);
    bands
        .par_iter()
        .map(|&r0| {
            let r1 = (r0 + B).min(rows.len());
            let mut t = 0u128;
            // walk the band column by column: the complements of one column of the band
            // are consecutive entries of one row (complement reverses colex order)
            for col in 0..maxlen {
                let mut acc = 0u128;
                for &(row, start, len) in &rows[r0..r1] {
                    if col >= len {
                        continue;
                    }
                    let g = unsafe { d.get_unchecked(start + col).get() };
                    let f = unsafe { d.get_unchecked(even_comp(bl, cc, row, col)).get() };
                    debug_assert_eq!(even_comp(bl, cc, row, col), {
                        let (l, r) = entry(lay, bl, row, col);
                        sh.index(lay, full ^ lay.compose(l, bl.c, r))
                    });
                    acc += weight(bl, row, col) as u128 * g * f;
                }
                t = md(t + md(acc, ring), ring);
            }
            t
        })
        .reduce(|| 0u128, |a, b| md(a + b, ring))
}

/// Odd `N`, fused: contribution of block `bl` of layer `k+1` (computed in tiles,
/// never stored), `Σ_U w(U) g(U) g(U^c)` with `U^c` in layer `k` = `ps`/`pd`.
fn odd_block_sum<W: Word>(lay: &Layout, chk: &crate::rule::Checker, ring: Ring, ps: &Shape, pd: &[W], bl: &Block) -> u128 {
    let h = lay.h;
    let full = lay.full();
    let rows = block_rows(lay, bl);
    if bl.i < bl.j {
        const TR: usize = 16;
        let ci = lay.binom[h][bl.i] as usize;
        let cj = lay.binom[h][bl.j] as usize;
        let sl = ps.slot[2 * (h - bl.j) + (1 - bl.c)];
        debug_assert_eq!(sl.rowlen, ci);
        let tiles: Vec<usize> = (0..ci).step_by(TR).collect();
        tiles
            .par_iter()
            .map_init(Vec::<W>::new, |tmp, &r0| {
                let nr = TR.min(ci - r0);
                tmp.clear();
                tmp.resize(nr * cj, W::default());
                for q0 in (0..nr).step_by(tile_rows(bl)) {
                    let q1 = (q0 + tile_rows(bl)).min(nr);
                    offdiag_tile(lay, chk, ring, ps, pd, bl, r0 + q0, r0 + q1, &mut tmp[q0 * cj..q1 * cj]);
                }
                let mut t = 0u128;
                for col in 0..cj {
                    let base = sl.off + (cj - 1 - col) * ci + (ci - 1 - r0);
                    let mut acc = 0u128;
                    for q in 0..nr {
                        acc += tmp[q * cj + col].get() * unsafe { pd.get_unchecked(base - q).get() };
                    }
                    t = md(t + md(acc, ring), ring);
                }
                md(2 * t, ring)
            })
            .reduce(|| 0u128, |a, b| md(a + b, ring))
    } else {
        let ci = rows.len();
        // complement block (h-i, h-i, 1-c) of layer k, a triangle with the same C
        let coff = ps.slot[2 * (h - bl.i) + 1 - bl.c].off;
        let tiles: Vec<usize> = (0..ci).step_by(DT).collect();
        tiles
            .par_iter()
            .map_init(Vec::<W>::new, |tmp, &r0| {
                let r1 = (r0 + DT).min(ci);
                let base = r0 * (r0 + 1) / 2;
                tmp.clear();
                tmp.resize(r1 * (r1 + 1) / 2 - base, W::default());
                diag_tile(lay, chk, ring, ps, pd, bl, r0, r1, tmp);
                let mut t = 0u128;
                // column by column: the complements of one column are consecutive
                for col in 0..r1 {
                    let mut acc = 0u128;
                    for row in r0.max(col)..r1 {
                        let gu = tmp[row * (row + 1) / 2 + col - base].get();
                        if gu == 0 {
                            continue;
                        }
                        let m2 = ci - 1 - col;
                        let ix = coff + m2 * (m2 + 1) / 2 + (ci - 1 - row);
                        debug_assert_eq!(ix, {
                            let (l, r) = entry(lay, bl, row, col);
                            ps.index(lay, full ^ lay.compose(l, bl.c, r))
                        });
                        let f = unsafe { pd.get_unchecked(ix).get() };
                        acc += weight(bl, row, col) as u128 * gu * f;
                    }
                    t = md(t + md(acc, ring), ring);
                }
                t
            })
            .reduce(|| 0u128, |a, b| md(a + b, ring))
    }
}

/// Peak resident set size of this process so far (`VmHWM`), in bytes.
pub fn peak_rss() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).map(|l| l.split_whitespace().nth(1).unwrap().parse::<u64>().unwrap() * 1024))
        .unwrap_or(0)
}

/// Simulated peak (in words) of the block-streamed count, without computing anything.
pub fn predicted_peak(n: usize) -> usize {
    let lay = Layout::new(n);
    let mut peak = 0;
    for k in 1..=n / 2 + (n % 2) {
        let (ps, os) = (Shape::new(&lay, k - 1), Shape::new(&lay, k));
        let needs = needs_for(&lay, &ps, &os, n, k);
        let last_even = n % 2 == 0 && k == n / 2;
        let last_odd = n % 2 == 1 && k == n / 2 + 1;
        let mode = if last_odd { 0 } else if last_even { 1 } else { 2 };
        let (_, _, p) = schedule(&ps, &os, &needs, mode);
        peak = peak.max(p);
    }
    peak
}

fn needs_for(lay: &Layout, ps: &Shape, os: &Shape, n: usize, k: usize) -> Vec<Vec<usize>> {
    let h = lay.h;
    os.blocks
        .iter()
        .map(|bl| {
            let mut v = pull_needs(ps, bl);
            if n % 2 == 1 && k == n / 2 + 1 {
                // complement block of layer k-1 = n/2
                let cb = find(ps, (h - bl.j) as isize, (h - bl.i) as isize, 1 - bl.c).expect("complement block");
                v.push(cb);
                v.sort();
                v.dedup();
            }
            v
        })
        .collect()
}

/// Full block-streamed count.  Returns `a(N)` (exact, or mod `ring.modulus`).
pub fn count<W: Word>(n: usize, chk: &crate::rule::Checker, ring: Ring, verbose: bool) -> u128 {
    assert!(W::BYTES <= 8, "block kernels accumulate in u64");
    let lay = Layout::new(n);
    let t0 = Instant::now();
    let mut ps = Shape::new(&lay, 0);
    let mut pr: Region<W> = Region::new(1);
    unsafe { pr.part(0, 1)[0] = W::put(1) };
    let klast = n / 2 + (n % 2); // the last (streamed) layer
    if n <= 1 {
        return 1;
    }
    for k in 1..=klast {
        let os = Shape::new(&lay, k);
        let needs = needs_for(&lay, &ps, &os, n, k);
        let last = k == klast;
        let mode = if !last { 2 } else if n % 2 == 0 { 1 } else { 0 };
        let (order, lastuse, peak) = schedule(&ps, &os, &needs, mode);
        let mut free_after: Vec<Vec<usize>> = vec![vec![]; order.len()];
        for (p, &t) in lastuse.iter().enumerate() {
            if t != usize::MAX {
                free_after[t].push(p);
            } else {
                let b = ps.blocks[p];
                pr.release(b.off, b.len);
            }
        }
        if !last {
            let or: Region<W> = Region::new(os.len);
            let mut tdiag = 0.0;
            let mut ndiag = 0usize;
            for (t, &b) in order.iter().enumerate() {
                let tb = Instant::now();
                compute_block(&lay, chk, ring, &ps, pr.data(), &os.blocks[b], &or);
                if os.blocks[b].i == os.blocks[b].j {
                    tdiag += tb.elapsed().as_secs_f64();
                    ndiag += os.blocks[b].len;
                }
                for &p in &free_after[t] {
                    let pb = ps.blocks[p];
                    pr.release(pb.off, pb.len);
                }
            }
            if verbose {
                eprintln!(
                    "  layer {:2}: {:>12} orbits ({:.2} GB) sim.peak {:.2} GB rss.peak {:.2} GB diag {} orbits {:.1}s t={:.1}s",
                    k,
                    os.len,
                    (os.len * W::BYTES) as f64 / 1e9,
                    (peak * W::BYTES) as f64 / 1e9,
                    peak_rss() as f64 / 1e9,
                    ndiag,
                    tdiag,
                    t0.elapsed().as_secs_f64()
                );
            }
            drop(std::mem::replace(&mut pr, or));
            ps = os;
        } else {
            let mut total = 0u128;
            if n % 2 == 0 {
                let or: Region<W> = Region::new(os.len);
                for (t, &b) in order.iter().enumerate() {
                    let bl = os.blocks[b];
                    compute_block(&lay, chk, ring, &ps, pr.data(), &bl, &or);
                    for &p in &free_after[t] {
                        let pb = ps.blocks[p];
                        pr.release(pb.off, pb.len);
                    }
                    total = md(total + even_block_sum(&lay, ring, &os, or.data(), &bl), ring);
                    or.release(bl.off, bl.len);
                }
            } else {
                for (t, &b) in order.iter().enumerate() {
                    let bl = os.blocks[b];
                    total = md(total + odd_block_sum(&lay, chk, ring, &ps, pr.data(), &bl), ring);
                    for &p in &free_after[t] {
                        let pb = ps.blocks[p];
                        pr.release(pb.off, pb.len);
                    }
                }
            }
            if verbose {
                eprintln!(
                    "  layer {:2} streamed + combined: rss.peak {:.2} GB t={:.1}s",
                    k,
                    peak_rss() as f64 / 1e9,
                    t0.elapsed().as_secs_f64()
                );
            }
            return total;
        }
    }
    unreachable!()
}
