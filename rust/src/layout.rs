//! Dense indexing of mirror orbits of `k`-subsets of `[0, N)`.
//!
//! Write `h = floor(N/2)`.  A set `S` is split into
//!   * `L = S ∩ [0, h)` (left half, as an `h`-bit mask),
//!   * `c = [h ∈ S]` (middle panel, only when `N` is odd),
//!   * `R` = the right half `S ∩ [N-h, N)` *reversed*, so bit `q` of `R` is panel `N-1-q`.
//!
//! The mirror `p ↦ N-1-p` then just swaps `L` and `R`.  With `i = |L|`, `j = |R|`,
//! the orbit representative is the one with `(i, rank L) ≤ (j, rank R)`
//! lexicographically, where `rank` is the colex rank among `h`-bit masks of the same
//! popcount (a table lookup).  The orbit representatives of layer `k` are stored
//! block by block:
//!   * block `(i, j, c)` with `i < j`: a full `C(h,i) × C(h,j)` matrix, row = rank L,
//!   * block `(i, i, c)`: a triangle, row `ρ = rank R`, column `rank L ≤ ρ`.
//!
//! So a layer needs `≈ C(N,k)/2` words and `index()` is `O(1)` with two `2^h` tables.

pub struct Layout {
    pub n: usize,
    pub h: usize,
    /// 1 if `N` is odd (there is a middle panel), else 0.
    pub b: usize,
    pub low: u64,
    /// colex rank of an `h`-bit mask among the masks of the same popcount
    pub rank: Vec<u32>,
    /// bit-reversal of an `h`-bit mask
    pub rev: Vec<u32>,
    /// `un[i]` = all `h`-bit masks of popcount `i`, increasing (= colex order)
    pub un: Vec<Vec<u32>>,
    pub binom: Vec<Vec<u64>>,
}

impl Layout {
    pub fn new(n: usize) -> Self {
        assert!(n >= 1 && n <= 50, "N out of range");
        let h = n / 2;
        let b = n % 2;
        let size = 1usize << h;
        let mut un: Vec<Vec<u32>> = vec![Vec::new(); h + 1];
        let mut rank = vec![0u32; size];
        let mut rev = vec![0u32; size];
        for m in 0..size {
            let pc = (m as u32).count_ones() as usize;
            rank[m] = un[pc].len() as u32;
            un[pc].push(m as u32);
            rev[m] = if h == 0 { 0 } else { (m as u32).reverse_bits() >> (32 - h) };
        }
        let mut binom = vec![vec![0u64; 65]; 65];
        for a in 0..65 {
            binom[a][0] = 1;
            for c in 1..=a {
                binom[a][c] = binom[a - 1][c - 1] + if c < a { binom[a - 1][c] } else { 0 };
            }
        }
        Layout { n, h, b, low: (size as u64) - 1, rank, rev, un, binom }
    }

    #[inline(always)]
    pub fn compose(&self, l: u32, c: usize, r: u32) -> u64 {
        l as u64 | (c as u64) << self.h | (self.rev[r as usize] as u64) << (self.n - self.h)
    }

    #[inline(always)]
    pub fn split(&self, s: u64) -> (u32, usize, u32) {
        let l = (s & self.low) as u32;
        let c = if self.b == 1 { ((s >> self.h) & 1) as usize } else { 0 };
        let r = self.rev[(s >> (self.n - self.h)) as usize];
        (l, c, r)
    }

    pub fn full(&self) -> u64 {
        if self.n == 64 { u64::MAX } else { (1u64 << self.n) - 1 }
    }
}

#[derive(Clone, Copy, Default, Debug)]
pub struct Slot {
    pub off: usize,
    /// row length for an off-diagonal block (= C(h, j))
    pub rowlen: usize,
    pub valid: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct Block {
    pub i: usize,
    pub j: usize,
    pub c: usize,
    pub off: usize,
    pub len: usize,
}

/// Index structure of one layer (independent of the stored values).
pub struct Shape {
    pub k: usize,
    pub blocks: Vec<Block>,
    /// `slot[2*i + c]` for the canonical block `(i, k-c-i, c)`
    pub slot: Vec<Slot>,
    pub len: usize,
}

impl Shape {
    pub fn new(lay: &Layout, k: usize) -> Self {
        let h = lay.h;
        let mut blocks = Vec::new();
        let mut slot = vec![Slot::default(); 2 * (h + 1)];
        let mut off = 0usize;
        for c in 0..=lay.b {
            if k < c {
                continue;
            }
            for i in 0..=h {
                if i + c > k {
                    break;
                }
                let j = k - c - i;
                if j > h || i > j {
                    continue;
                }
                let ci = lay.binom[h][i] as usize;
                let cj = lay.binom[h][j] as usize;
                let len = if i < j { ci * cj } else { ci * (ci + 1) / 2 };
                slot[2 * i + c] = Slot { off, rowlen: cj, valid: true };
                blocks.push(Block { i, j, c, off, len });
                off += len;
            }
        }
        Shape { k, blocks, slot, len: off }
    }

    /// Position of the orbit of `s` (which must have popcount `k`).
    #[inline(always)]
    pub fn index(&self, lay: &Layout, s: u64) -> usize {
        let (l, c, r) = lay.split(s);
        self.index_parts(lay, l, c, r)
    }

    #[inline(always)]
    pub fn index_parts(&self, lay: &Layout, l: u32, c: usize, r: u32) -> usize {
        let i = l.count_ones() as usize;
        let j = r.count_ones() as usize;
        let rl = lay.rank[l as usize] as usize;
        let rr = lay.rank[r as usize] as usize;
        if i < j {
            let sl = unsafe { self.slot.get_unchecked(2 * i + c) };
            sl.off + rl * sl.rowlen + rr
        } else if i > j {
            let sl = unsafe { self.slot.get_unchecked(2 * j + c) };
            sl.off + rr * sl.rowlen + rl
        } else {
            let sl = unsafe { self.slot.get_unchecked(2 * i + c) };
            let (a, m) = if rl <= rr { (rl, rr) } else { (rr, rl) };
            sl.off + m * (m + 1) / 2 + a
        }
    }

    /// Iterate rows: `(block, row index, start offset, row length)`.
    pub fn rows(&self, lay: &Layout) -> Vec<(Block, usize, usize, usize)> {
        let h = lay.h;
        let mut out = Vec::new();
        for bl in &self.blocks {
            let ci = lay.binom[h][bl.i] as usize;
            if bl.i < bl.j {
                let cj = lay.binom[h][bl.j] as usize;
                for row in 0..ci {
                    out.push((*bl, row, bl.off + row * cj, cj));
                }
            } else {
                for row in 0..ci {
                    out.push((*bl, row, bl.off + row * (row + 1) / 2, row + 1));
                }
            }
        }
        out
    }
}

/// The `(L, R)` masks of entry `col` of row `row` in block `bl`.
#[inline(always)]
pub fn entry(lay: &Layout, bl: &Block, row: usize, col: usize) -> (u32, u32) {
    if bl.i < bl.j {
        (lay.un[bl.i][row], lay.un[bl.j][col])
    } else {
        (lay.un[bl.i][col], lay.un[bl.i][row])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn index_is_orbit_bijection() {
        for n in 1..=13 {
            let lay = Layout::new(n);
            for k in 0..=n {
                let sh = Shape::new(&lay, k);
                let mut seen = vec![false; sh.len];
                let mut orbits = 0;
                for s in 0u64..(1 << n) {
                    if s.count_ones() as usize != k {
                        continue;
                    }
                    let m = s.reverse_bits() >> (64 - n);
                    let ix = sh.index(&lay, s);
                    assert_eq!(ix, sh.index(&lay, m));
                    if s <= m {
                        assert!(!seen[ix]);
                        seen[ix] = true;
                        orbits += 1;
                    }
                }
                assert_eq!(orbits, sh.len);
                // rows/entry enumerate each slot once and map back to the same index
                for (bl, row, start, len) in sh.rows(&lay) {
                    for col in 0..len {
                        let (l, r) = entry(&lay, &bl, row, col);
                        assert_eq!(sh.index_parts(&lay, l, bl.c, r), start + col);
                    }
                }
            }
        }
    }
}
