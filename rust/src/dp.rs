//! Layered subset DP over mirror orbits, and the meet-in-the-middle count.
//!
//! `g(S)` = number of valid orderings that build `S`.  Pull form:
//! `g(T) = Σ_{p ∈ T, (T\p, p) valid} g(T \ p)`, so each entry of layer `k` is written
//! exactly once from layer `k-1` (no atomics; rows are processed in parallel).
//!
//! Exactness: `g(T) ≤ |T|!`, so `u64` is exact for every layer `k ≤ 20` (all `N ≤ 41`
//! in the meet-in-the-middle).  The `u32` storage computes everything mod `m < 2^32`
//! (or `m = 2^32`) for a CRT reconstruction with half the memory.

use crate::layout::{entry, Layout, Shape};
use crate::rule::Checker;
use rayon::prelude::*;

pub trait Word: Copy + Send + Sync + Default + 'static {
    fn get(self) -> u128;
    fn put(x: u128) -> Self;
    /// low 64 bits (the block kernels accumulate in `u64`: exact sums are values of
    /// `g ≤ 20!`, modular sums are `< 64 · 2^32`)
    fn get64(self) -> u64;
    const BYTES: usize;
}
macro_rules! word {
    ($t:ty) => {
        impl Word for $t {
            #[inline(always)]
            fn get(self) -> u128 {
                self as u128
            }
            #[inline(always)]
            fn get64(self) -> u64 {
                self as u64
            }
            #[inline(always)]
            fn put(x: u128) -> Self {
                debug_assert!(x <= <$t>::MAX as u128);
                x as $t
            }
            const BYTES: usize = std::mem::size_of::<$t>();
        }
    };
}
word!(u8);
word!(u16);
word!(u32);
word!(u64);
word!(u128);

/// Arithmetic domain: exact (`modulus == 0`, `u64` words) or mod `modulus`.
#[derive(Clone, Copy, Debug)]
pub struct Ring {
    pub modulus: u64,
    /// `floor(2^64 / modulus)` for Barrett reduction (a 64-bit `div` per entry costs
    /// 40-90 cycles, a large share of the inner loop)
    minv: u64,
}
impl Ring {
    pub fn new(modulus: u64) -> Self {
        assert!(modulus == 0 || (2..=1 << 32).contains(&modulus));
        let minv = if modulus == 0 { 0 } else { ((1u128 << 64) / modulus as u128) as u64 };
        Ring { modulus, minv }
    }
    pub const EXACT: Ring = Ring { modulus: 0, minv: 0 };
    /// `a mod modulus` for `a < 2^64` (modular mode only).
    #[inline(always)]
    pub fn red64(self, a: u64) -> u64 {
        let q = ((a as u128 * self.minv as u128) >> 64) as u64;
        let mut r = a - q * self.modulus;
        while r >= self.modulus {
            r -= self.modulus;
        }
        r
    }
    #[inline(always)]
    pub fn red(self, x: u128) -> u128 {
        // in modular mode the accumulator is a sum of < 64 residues < 2^32
        if self.modulus == 0 { x } else { self.red64(x as u64) as u128 }
    }
    /// Reduce any `u128` (exact mode: identity).
    #[inline(always)]
    pub fn red_any(self, x: u128) -> u128 {
        if self.modulus == 0 {
            x
        } else if x >> 64 == 0 {
            self.red64(x as u64) as u128
        } else {
            x % self.modulus as u128
        }
    }
}

pub struct Layer<W: Word> {
    pub shape: Shape,
    pub data: Vec<W>,
}

impl<W: Word> Layer<W> {
    #[inline(always)]
    pub fn at(&self, lay: &Layout, s: u64) -> u128 {
        unsafe { self.data.get_unchecked(self.shape.index(lay, s)).get() }
    }
}

pub fn layer0<W: Word>(lay: &Layout) -> Layer<W> {
    let shape = Shape::new(lay, 0);
    let mut data: Vec<W> = zeroed_vec(shape.len);
    data[0] = W::put(1);
    Layer { shape, data }
}

/// Compute layer `k = prev.k + 1` by pulling from `prev`.
pub fn step<W: Word>(lay: &Layout, chk: &Checker, ring: Ring, prev: &Layer<W>) -> Layer<W> {
    step_into(lay, chk, ring, prev, Vec::new())
}

/// As [`step`], reusing `buf` as storage when it is large enough (every entry is
/// overwritten, so stale contents are harmless).  Ping-ponging two buffers avoids
/// paying the page faults of a fresh multi-GB allocation at every layer.
pub fn step_into<W: Word>(
    lay: &Layout,
    chk: &Checker,
    ring: Ring,
    prev: &Layer<W>,
    mut buf: Vec<W>,
) -> Layer<W> {
    let k = prev.shape.k + 1;
    let shape = Shape::new(lay, k);
    let mut data: Vec<W> = if buf.len() >= shape.len {
        buf.truncate(shape.len);
        buf
    } else {
        drop(buf);
        zeroed_vec(shape.len)
    };
    let rows = shape.rows(lay);
    // carve the output into row slices
    let mut slices: Vec<(crate::layout::Block, usize, &mut [W])> = Vec::with_capacity(rows.len());
    {
        let mut rest: &mut [W] = &mut data;
        let mut pos = 0usize;
        // rows are in increasing offset order
        for (bl, row, start, len) in rows {
            debug_assert_eq!(start, pos);
            let (a, b) = rest.split_at_mut(len);
            slices.push((bl, row, a));
            rest = b;
            pos += len;
        }
    }
    let ps = &prev.shape;
    let pd = &prev.data;
    slices.into_par_iter().with_min_len(4).for_each(|(bl, row, out)| {
        if bl.i < bl.j {
            offdiag_row(lay, chk, ring, ps, pd, &bl, row, out);
        } else {
            generic_row(lay, chk, ring, ps, pd, &bl, row, out);
        }
    });
    Layer { shape, data }
}

/// Row of an off-diagonal block `(i < j, c)`: `L` is fixed, `R` runs over all
/// `j`-subsets in colex order.  Every predecessor `T \ p` lives in a row that is
/// either streamed in lock-step with the output (`p ∈ L`, or `p` = middle) or is a
/// single row of length `≤ C(h, h/2)` read at random (`p ∈ R`), which stays in cache.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub(crate) fn offdiag_row<W: Word>(
    lay: &Layout,
    chk: &Checker,
    ring: Ring,
    ps: &Shape,
    pd: &[W],
    bl: &crate::layout::Block,
    row: usize,
    out: &mut [W],
) {
    let (i, j, c, h) = (bl.i, bl.j, bl.c, lay.h);
    let l = lay.un[i][row];
    // streams for removals from L (block (i-1, j, c), always canonical)
    let mut lx = [(0u32, 0usize); 32];
    let mut nl = 0;
    if i > 0 {
        let sl = ps.slot[2 * (i - 1) + c];
        let mut bits = l;
        while bits != 0 {
            let x = bits.trailing_zeros();
            bits &= bits - 1;
            lx[nl] = (x, sl.off + lay.rank[(l ^ (1 << x)) as usize] as usize * sl.rowlen);
            nl += 1;
        }
    }
    // stream for removing the middle panel (block (i, j, 0))
    let midbase = if c == 1 {
        let sl = ps.slot[2 * i];
        sl.off + row * sl.rowlen
    } else {
        0
    };
    // row for removals from R (block (i, j-1, c)) when it is off-diagonal
    let rbase = if i < j - 1 {
        let sl = ps.slot[2 * i + c];
        Some(sl.off + row * sl.rowlen)
    } else {
        None
    };
    let rshift = lay.n - 1;
    let un_j = &lay.un[j];
    let rrem = &lay.rrem[j];
    for (col, o) in out.iter_mut().enumerate() {
        let r = unsafe { *un_j.get_unchecked(col) };
        let t = lay.compose_col(l, c, j, col);
        let mut acc = 0u128;
        for &(x, base) in &lx[..nl] {
            if chk.valid(t ^ (1u64 << x), x) {
                acc += unsafe { pd.get_unchecked(base + col).get() };
            }
        }
        if c == 1 && chk.valid(t ^ (1u64 << h), h as u32) {
            acc += unsafe { pd.get_unchecked(midbase + col).get() };
        }
        let mut bits = r;
        let mut q = col * j;
        while bits != 0 {
            let y = bits.trailing_zeros();
            bits &= bits - 1;
            let p = (rshift - y as usize) as u32;
            q += 1;
            if chk.valid(t ^ (1u64 << p), p) {
                let ix = match rbase {
                    Some(b) => b + unsafe { *rrem.get_unchecked(q - 1) } as usize,
                    None => ps.index_parts(lay, l, c, r ^ (1 << y)),
                };
                acc += unsafe { pd.get_unchecked(ix).get() };
            }
        }
        *o = W::put(ring.red(acc));
    }
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub(crate) fn generic_row<W: Word>(
    lay: &Layout,
    chk: &Checker,
    ring: Ring,
    ps: &Shape,
    pd: &[W],
    bl: &crate::layout::Block,
    row: usize,
    out: &mut [W],
) {
    {
        for (col, o) in out.iter_mut().enumerate() {
            let (l, r) = entry(lay, bl, row, col);
            let t = lay.compose(l, bl.c, r);
            let mut acc = 0u128;
            let mut bits = t;
            while bits != 0 {
                let p = bits.trailing_zeros();
                bits &= bits - 1;
                let s = t ^ (1u64 << p);
                if chk.valid(s, p) {
                    acc += unsafe { pd.get_unchecked(ps.index(lay, s)).get() };
                }
            }
            *o = W::put(ring.red(acc));
        }
    }
}

/// Weight of an orbit representative = orbit size (1 if mirror-symmetric, else 2).
#[inline(always)]
pub fn weight(bl: &crate::layout::Block, row: usize, col: usize) -> u64 {
    if bl.i == bl.j && row == col { 1 } else { 2 }
}

/// `Σ_{|S|=k} g(S)` (number of valid prefixes of length `k`), mod `ring` (or exact).
pub fn layer_sum<W: Word>(lay: &Layout, ring: Ring, layer: &Layer<W>) -> u128 {
    let rows = layer.shape.rows(lay);
    let m = ring.modulus as u128;
    rows.par_iter()
        .map(|&(bl, row, start, len)| {
            let mut t = 0u128;
            for col in 0..len {
                t += weight(&bl, row, col) as u128 * layer.data[start + col].get();
            }
            if m != 0 { t % m } else { t }
        })
        .reduce(|| 0u128, |a, b| if m != 0 { (a + b) % m } else { a + b })
}

/// Meet in the middle.  `layer` must be layer `floor(N/2)`.
///  * even `N = 2k`:  `a = Σ_{|S|=k} g(S) g(S^c)`
///  * odd `N = 2k+1`: `a = Σ_{|S|=k} g(S) Σ_{p∉S, (S,p) valid} g((S ∪ p)^c)`
///
/// both using `f(S) = g(S^c)` (reversal symmetry).  The summand is mirror invariant,
/// so we sum over orbit representatives with the orbit size as weight.
pub fn combine<W: Word>(lay: &Layout, chk: &Checker, ring: Ring, layer: &Layer<W>) -> u128 {
    let n = lay.n;
    assert_eq!(layer.shape.k, n / 2);
    let full = lay.full();
    let rows = layer.shape.rows(lay);
    let m = ring.modulus as u128;
    let odd = n % 2 == 1;
    rows.par_iter()
        .map(|&(bl, row, start, len)| {
            let mut t = 0u128;
            for col in 0..len {
                let gs = layer.data[start + col].get();
                if gs == 0 {
                    continue;
                }
                let (l, r) = entry(lay, &bl, row, col);
                let s = lay.compose(l, bl.c, r);
                let comp = full ^ s;
                let f: u128 = if !odd {
                    layer.at(lay, comp)
                } else {
                    let mut f = 0u128;
                    let mut bits = comp;
                    while bits != 0 {
                        let p = bits.trailing_zeros();
                        bits &= bits - 1;
                        if chk.valid(s, p) {
                            f += layer.at(lay, comp ^ (1u64 << p));
                        }
                    }
                    if m != 0 { f % m } else { f }
                };
                let term = weight(&bl, row, col) as u128 * gs * f;
                t = if m != 0 { (t + term % m) % m } else { t + term };
            }
            t
        })
        .reduce(|| 0u128, |a, b| if m != 0 { (a + b) % m } else { a + b })
}

/// Odd `N = 2k+1`, fused form: `a = Σ_{|U|=k+1} g(U) g(U^c)` with `U^c` in layer `k`.
/// Layer `k+1` is computed row by row into a small scratch buffer and consumed at
/// once, so it is never stored.  Per entry this needs one random lookup (`g(U^c)`)
/// instead of the `≈ k/2` random lookups of the direct odd formula, and the pulls
/// into layer `k` use the cache-friendly row kernels.
pub fn combine_odd_fused<W: Word>(lay: &Layout, chk: &Checker, ring: Ring, layer: &Layer<W>) -> u128 {
    let n = lay.n;
    assert!(n % 2 == 1 && layer.shape.k == n / 2);
    let full = lay.full();
    let shape = Shape::new(lay, layer.shape.k + 1);
    let rows = shape.rows(lay);
    let m = ring.modulus as u128;
    let (ps, pd) = (&layer.shape, &layer.data[..]);
    let h = lay.h;
    // Off-diagonal blocks: tiles of TR consecutive rows.  For U = (L, c, R) the
    // complement sits in block (h-j, h-i, 1-c) at row C(h,j)-1-rank R and column
    // C(h,i)-1-rank L (complementing reverses colex order), so walking a tile
    // column by column reads short contiguous runs instead of one cache miss per entry.
    const TR: usize = 16;
    let mut tiles: Vec<(crate::layout::Block, usize, usize, usize)> = Vec::new();
    for &(bl, row, _start, len) in &rows {
        if bl.i < bl.j {
            match tiles.last_mut() {
                Some(t) if t.0.off == bl.off && t.1 + t.2 == row && t.2 < TR => t.2 += 1,
                _ => tiles.push((bl, row, 1, len)),
            }
        }
    }
    let off_sum = tiles
        .par_iter()
        .map_init(Vec::<W>::new, |tmp, &(bl, r0, nr, len)| {
            tmp.clear();
            tmp.resize(nr * len, W::default());
            for q in 0..nr {
                offdiag_row(lay, chk, ring, ps, pd, &bl, r0 + q, &mut tmp[q * len..(q + 1) * len]);
            }
            let ci = lay.binom[h][bl.i] as usize;
            let cj = lay.binom[h][bl.j] as usize;
            let sl = ps.slot[2 * (h - bl.j) + (1 - bl.c)];
            debug_assert_eq!(sl.rowlen, ci);
            let mut t = 0u128;
            for col in 0..len {
                let base = sl.off + (cj - 1 - col) * ci + (ci - 1 - r0);
                let mut acc = 0u128;
                for q in 0..nr {
                    let gu = tmp[q * len + col].get();
                    acc += gu * unsafe { pd.get_unchecked(base - q).get() };
                }
                t = if m != 0 { (t + acc % m) % m } else { t + acc };
            }
            if m != 0 { 2 * t % m } else { 2 * t }
        })
        .reduce(|| 0u128, |a, b| if m != 0 { (a + b) % m } else { a + b });
    let diag_rows: Vec<_> = rows.iter().filter(|r| r.0.i == r.0.j).copied().collect();
    let diag_sum = diag_rows
        .par_iter()
        .with_min_len(4)
        .map_init(Vec::<W>::new, |tmp, &(bl, row, _start, len)| {
            tmp.clear();
            tmp.resize(len, W::default());
            generic_row(lay, chk, ring, ps, pd, &bl, row, tmp);
            let mut t = 0u128;
            for col in 0..len {
                let gu = tmp[col].get();
                if gu == 0 {
                    continue;
                }
                let (l, r) = entry(lay, &bl, row, col);
                let u = lay.compose(l, bl.c, r);
                let term = weight(&bl, row, col) as u128 * gu * layer.at(lay, full ^ u);
                t = if m != 0 { (t + term) % m } else { t + term };
            }
            t
        })
        .reduce(|| 0u128, |a, b| if m != 0 { (a + b) % m } else { a + b });
    if m != 0 { (off_sum + diag_sum) % m } else { off_sum + diag_sum }
}

/// Full meet-in-the-middle count.  Returns `a(N)` (exact, or mod `ring.modulus`).
pub fn count<W: Word>(n: usize, chk: &Checker, ring: Ring, verbose: bool) -> u128 {
    count_impl::<W>(n, chk, ring, verbose, true)
}

/// As [`count`] but with the direct (unfused) odd-`N` combination; for cross-checks.
pub fn count_direct<W: Word>(n: usize, chk: &Checker, ring: Ring) -> u128 {
    count_impl::<W>(n, chk, ring, false, false)
}

fn count_impl<W: Word>(n: usize, chk: &Checker, ring: Ring, verbose: bool, fused: bool) -> u128 {
    let lay = Layout::new(n);
    let mut cur: Layer<W> = layer0(&lay);
    let t0 = std::time::Instant::now();
    // two buffers of the largest layer size, used alternately
    let maxlen = Shape::new(&lay, n / 2).len;
    let mut spare: Vec<W> = if n >= 8 { zeroed_vec(maxlen) } else { Vec::new() };
    for q in 0..n / 2 {
        let next = step_into(&lay, chk, ring, &cur, spare);
        spare = std::mem::take(&mut cur.data);
        if q == 0 && n >= 8 {
            spare = zeroed_vec(maxlen);
        }
        if 2 * (q + 2) > n {
            spare = Vec::new(); // the last layer needs no further buffer
        }
        cur = next;
        if verbose {
            eprintln!(
                "  layer {:2}: {:>12} orbits ({:.2} GB) t={:.1}s",
                cur.shape.k,
                cur.shape.len,
                (cur.shape.len * W::BYTES) as f64 / 1e9,
                t0.elapsed().as_secs_f64()
            );
        }
    }
    let t1 = std::time::Instant::now();
    let a = if fused && n % 2 == 1 {
        combine_odd_fused(&lay, chk, ring, &cur)
    } else {
        combine(&lay, chk, ring, &cur)
    };
    if verbose {
        eprintln!("  combine: {:.1}s", t1.elapsed().as_secs_f64());
    }
    a
}

unsafe extern "C" {
    fn madvise(addr: *mut std::ffi::c_void, len: usize, advice: i32) -> i32;
}
const MADV_HUGEPAGE: i32 = 14;

/// A zeroed vector whose (still untouched, calloc/mmap-backed) pages are marked for
/// transparent huge pages: big layers otherwise spend a lot of system time in
/// 4 KiB page faults.
pub fn zeroed_vec<W: Word>(len: usize) -> Vec<W> {
    let v: Vec<W> = vec![W::default(); len];
    let bytes = len * std::mem::size_of::<W>();
    if bytes >= 1 << 22 {
        let p = v.as_ptr() as usize;
        let start = (p + 0x1f_ffff) & !0x1f_ffff;
        let end = (p + bytes) & !0x1f_ffff;
        if end > start {
            unsafe {
                madvise(start as *mut _, end - start, MADV_HUGEPAGE);
            }
        }
    }
    v
}
