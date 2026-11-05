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
            fn put(x: u128) -> Self {
                debug_assert!(x <= <$t>::MAX as u128);
                x as $t
            }
            const BYTES: usize = std::mem::size_of::<$t>();
        }
    };
}
word!(u32);
word!(u64);
word!(u128);

/// Arithmetic domain: exact (`modulus == 0`, `u64` words) or mod `modulus`.
#[derive(Clone, Copy, Debug)]
pub struct Ring {
    pub modulus: u64,
}
impl Ring {
    #[inline(always)]
    pub fn red(self, x: u128) -> u128 {
        // in modular mode the accumulator is a sum of < 64 residues < 2^32
        if self.modulus == 0 { x } else { ((x as u64) % self.modulus) as u128 }
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
    let mut data = vec![W::default(); shape.len];
    data[0] = W::put(1);
    Layer { shape, data }
}

/// Compute layer `k = prev.k + 1` by pulling from `prev`.
pub fn step<W: Word>(lay: &Layout, chk: &Checker, ring: Ring, prev: &Layer<W>) -> Layer<W> {
    let k = prev.shape.k + 1;
    let shape = Shape::new(lay, k);
    let mut data: Vec<W> = vec![W::default(); shape.len];
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
        for (col, o) in out.iter_mut().enumerate() {
            let (l, r) = entry(lay, &bl, row, col);
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
    });
    Layer { shape, data }
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

/// Full meet-in-the-middle count.  Returns `a(N)` (exact, or mod `ring.modulus`).
pub fn count<W: Word>(n: usize, chk: &Checker, ring: Ring, verbose: bool) -> u128 {
    let lay = Layout::new(n);
    let mut cur: Layer<W> = layer0(&lay);
    let t0 = std::time::Instant::now();
    for _ in 0..n / 2 {
        let next = step(&lay, chk, ring, &cur);
        drop(cur);
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
    combine(&lay, chk, ring, &cur)
}
