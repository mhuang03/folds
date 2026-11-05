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

use crate::dp::{generic_row, offdiag_row, weight, Ring, Word};
use crate::layout::{entry, Block, Layout, Shape};
use rayon::prelude::*;
use std::time::Instant;

unsafe extern "C" {
    fn mmap(addr: *mut std::ffi::c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut std::ffi::c_void;
    fn munmap(addr: *mut std::ffi::c_void, len: usize) -> i32;
    fn madvise(addr: *mut std::ffi::c_void, len: usize, advice: i32) -> i32;
    fn mprotect(addr: *mut std::ffi::c_void, len: usize, prot: i32) -> i32;
}
const PROT_NONE: i32 = 0;
const PROT_RW: i32 = 3;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const MAP_NORESERVE: i32 = 0x4000;
const MADV_DONTNEED: i32 = 4;
const MADV_HUGEPAGE: i32 = 14;
const PAGE: usize = 4096;

/// A lazily backed array of `len` words (anonymous `mmap`, zero on first touch).
pub struct Region<W: Word> {
    ptr: *mut W,
    len: usize,
    bytes: usize,
}
unsafe impl<W: Word> Send for Region<W> {}
unsafe impl<W: Word> Sync for Region<W> {}

impl<W: Word> Region<W> {
    pub fn new(len: usize) -> Self {
        let bytes = (len.max(1) * W::BYTES + PAGE - 1) / PAGE * PAGE;
        let p = unsafe {
            mmap(std::ptr::null_mut(), bytes, PROT_RW, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0)
        };
        assert!(p as isize != -1, "mmap of {bytes} bytes failed");
        if bytes >= 1 << 22 {
            unsafe { madvise(p, bytes, MADV_HUGEPAGE) };
        }
        Region { ptr: p as *mut W, len, bytes }
    }
    #[inline(always)]
    pub fn data(&self) -> &[W] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
    /// Mutable view of `[start, start+len)`.  Callers hand out disjoint ranges only.
    #[allow(clippy::mut_from_ref)]
    #[inline(always)]
    unsafe fn part(&self, start: usize, len: usize) -> &mut [W] {
        debug_assert!(start + len <= self.len);
        unsafe { std::slice::from_raw_parts_mut(self.ptr.add(start), len) }
    }
    /// Give the pages lying entirely inside `[start, start+len)` back to the OS and
    /// make them inaccessible.
    pub fn release(&self, start: usize, len: usize) {
        let a = (self.ptr as usize + start * W::BYTES + PAGE - 1) / PAGE * PAGE;
        let b = (self.ptr as usize + (start + len) * W::BYTES) / PAGE * PAGE;
        if b > a {
            unsafe {
                madvise(a as *mut _, b - a, MADV_DONTNEED);
                mprotect(a as *mut _, b - a, PROT_NONE);
            }
        }
    }
}
impl<W: Word> Drop for Region<W> {
    fn drop(&mut self) {
        unsafe { munmap(self.ptr as *mut _, self.bytes) };
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
    let mut best: Option<(Vec<usize>, Vec<usize>, usize)> = None;
    for dec in [false, true] {
        let mut order: Vec<usize> = (0..out.blocks.len()).collect();
        order.sort_by_key(|&b| (out.blocks[b].i, out.blocks[b].c));
        if dec {
            order.reverse();
        }
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
            for p in 0..prev.blocks.len() {
                if last[p] == t {
                    live -= prev.blocks[p].len;
                }
            }
        }
        if best.as_ref().is_none_or(|x| peak < x.2) {
            best = Some((order, last, peak));
        }
    }
    best.unwrap()
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

/// Compute block `bl` of the layer `out_shape` into `out` from the layer `ps`/`pd`.
fn compute_block<W: Word>(lay: &Layout, chk: &crate::rule::Checker, ring: Ring, ps: &Shape, pd: &[W], bl: &Block, out: &Region<W>) {
    let rows = block_rows(lay, bl);
    rows.into_par_iter().with_min_len(4).for_each(|(row, start, len)| {
        let o = unsafe { out.part(start, len) };
        if bl.i < bl.j {
            offdiag_row(lay, chk, ring, ps, pd, bl, row, o);
        } else {
            generic_row(lay, chk, ring, ps, pd, bl, row, o);
        }
    });
}

#[inline(always)]
fn md(x: u128, m: u128) -> u128 {
    if m != 0 { x % m } else { x }
}

/// Even `N`: `Σ_{S in block} w(S) g(S) g(S^c)` where `S^c` lies in the same block.
fn even_block_sum<W: Word>(lay: &Layout, ring: Ring, sh: &Shape, d: &[W], bl: &Block) -> u128 {
    let full = lay.full();
    let m = ring.modulus as u128;
    let rows = block_rows(lay, bl);
    const B: usize = 32;
    let bands: Vec<usize> = (0..rows.len()).step_by(B).collect();
    let maxlen = rows.iter().map(|r| r.2).max().unwrap_or(0);
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
                    if g == 0 {
                        continue;
                    }
                    let (l, r) = entry(lay, bl, row, col);
                    let s = lay.compose(l, bl.c, r);
                    let f = unsafe { d.get_unchecked(sh.index(lay, full ^ s)).get() };
                    acc += weight(bl, row, col) as u128 * g * f;
                }
                t = md(t + md(acc, m), m);
            }
            t
        })
        .reduce(|| 0u128, |a, b| md(a + b, m))
}

/// Odd `N`, fused: contribution of block `bl` of layer `k+1` (computed in tiles,
/// never stored), `Σ_U w(U) g(U) g(U^c)` with `U^c` in layer `k` = `ps`/`pd`.
fn odd_block_sum<W: Word>(lay: &Layout, chk: &crate::rule::Checker, ring: Ring, ps: &Shape, pd: &[W], bl: &Block) -> u128 {
    let m = ring.modulus as u128;
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
                for q in 0..nr {
                    offdiag_row(lay, chk, ring, ps, pd, bl, r0 + q, &mut tmp[q * cj..(q + 1) * cj]);
                }
                let mut t = 0u128;
                for col in 0..cj {
                    let base = sl.off + (cj - 1 - col) * ci + (ci - 1 - r0);
                    let mut acc = 0u128;
                    for q in 0..nr {
                        acc += tmp[q * cj + col].get() * unsafe { pd.get_unchecked(base - q).get() };
                    }
                    t = md(t + md(acc, m), m);
                }
                md(2 * t, m)
            })
            .reduce(|| 0u128, |a, b| md(a + b, m))
    } else {
        rows.par_iter()
            .with_min_len(4)
            .map_init(Vec::<W>::new, |tmp, &(row, _start, len)| {
                tmp.clear();
                tmp.resize(len, W::default());
                generic_row(lay, chk, ring, ps, pd, bl, row, tmp);
                let mut t = 0u128;
                for col in 0..len {
                    let gu = tmp[col].get();
                    if gu == 0 {
                        continue;
                    }
                    let (l, r) = entry(lay, bl, row, col);
                    let u = lay.compose(l, bl.c, r);
                    let f = unsafe { pd.get_unchecked(ps.index(lay, full ^ u)).get() };
                    t = md(t + weight(bl, row, col) as u128 * gu * f, m);
                }
                t
            })
            .reduce(|| 0u128, |a, b| md(a + b, m))
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
    let lay = Layout::new(n);
    let m = ring.modulus as u128;
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
            for (t, &b) in order.iter().enumerate() {
                compute_block(&lay, chk, ring, &ps, pr.data(), &os.blocks[b], &or);
                for &p in &free_after[t] {
                    let pb = ps.blocks[p];
                    pr.release(pb.off, pb.len);
                }
            }
            if verbose {
                eprintln!(
                    "  layer {:2}: {:>12} orbits ({:.2} GB) sim.peak {:.2} GB rss.peak {:.2} GB t={:.1}s",
                    k,
                    os.len,
                    (os.len * W::BYTES) as f64 / 1e9,
                    (peak * W::BYTES) as f64 / 1e9,
                    peak_rss() as f64 / 1e9,
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
                    total = md(total + even_block_sum(&lay, ring, &os, or.data(), &bl), m);
                    or.release(bl.off, bl.len);
                }
            } else {
                for (t, &b) in order.iter().enumerate() {
                    let bl = os.blocks[b];
                    total = md(total + odd_block_sum(&lay, chk, ring, &ps, pr.data(), &bl), m);
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
