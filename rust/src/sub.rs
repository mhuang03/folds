//! Sub-block layout: blocks `(i, j, c)` of `layout.rs` split further by the exact
//! *high* parts of `L` and `R`.
//!
//! Write `h = floor(N/2)`, choose `t ≤ h` and `a = h - t`.  `L` (bit `q` = panel `q`)
//! is split into `Llo = L mod 2^a` and `HL = L >> a` (the `t` panels next to the
//! middle); `R` (bit `q` = panel `N-1-q`) likewise into `Rlo`, `HR`.  A sub-block is
//! `(c, HL, HR, il = |Llo|, jl = |Rlo|)`; it holds all sets with these high parts and
//! these low popcounts, as a `C(a,il) × C(a,jl)` matrix (row = colex rank of `Llo`,
//! column = colex rank of `Rlo`).  The mirror swaps `(il, HL) ↔ (jl, HR)`; the
//! canonical sub-block has `(il, HL) ≤ (jl, HR)` (lexicographic), and when they are
//! equal it is a triangle (row `ρ` = rank `Rlo`, column = rank `Llo ≤ ρ`), exactly as
//! the diagonal blocks of `layout.rs`.  With `t = 0` this *is* the block layout.
//!
//! The pull `g(T) = Σ_p g(T \ p)` reads, for a sub-block `X`:
//!   * `(c, HL, HR, il-1, jl)`: remove a low left panel (row `rank(Llo\x)`, same column),
//!   * `(c, HL\x, HR, il, jl)`: remove a high left panel (same row and column),
//!   * `(c, HL, HR, il, jl-1)`: remove a low right panel (same row, column `rank(Rlo\y)`),
//!   * `(c, HL, HR\y, il, jl)`: remove a high right panel (same row and column),
//!   * `(0, HL, HR, il, jl)`  : remove the middle panel,
//!
//! each possibly transposed or triangular after canonicalization.  So the DP is a
//! DAG on sub-blocks, and a sub-block can be freed after its last reader; the order
//! of the whole computation (across layers) is chosen by a simulated-peak search.

use crate::layout::Layout;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SB {
    pub c: u8,
    pub hl: u16,
    pub hr: u16,
    pub il: u8,
    pub jl: u8,
    /// `(il, HL) == (jl, HR)`: stored as a triangle
    pub tri: bool,
    pub off: usize,
    pub len: usize,
}

pub struct SubShape {
    pub k: usize,
    pub sbs: Vec<SB>,
    /// `idx[((c*T + hl)*T + hr)*(a+1) + il]` = sub-block index (canonical keys only)
    idx: Vec<u32>,
    pub len: usize,
}

pub struct SubLayout {
    pub n: usize,
    pub h: usize,
    pub b: usize,
    pub t: usize,
    pub a: usize,
    pub tt: usize,
    pub binom: Vec<Vec<u64>>,
    pub shapes: Vec<SubShape>,
}

/// Reference to a sub-block of some layer, with orientation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ref {
    pub ix: u32,
    /// the requested `(Llo, Rlo)` is stored as `(Rlo, Llo)`
    pub trans: bool,
}

impl SubLayout {
    pub fn new(n: usize, t: usize) -> Self {
        Self::aligned(n, t, 1)
    }
    /// As `new`, with every sub-block starting at a multiple of `align` words (a page,
    /// so that freeing a sub-block returns all of its pages).
    pub fn aligned(n: usize, t: usize, align: usize) -> Self {
        let lay = Layout::new(n.max(1));
        let (h, b) = (n / 2, n % 2);
        assert!(t <= h && t <= 12);
        let a = h - t;
        let tt = 1usize << t;
        let binom = lay.binom.clone();
        let mut shapes = Vec::new();
        for k in 0..=n {
            let mut sbs = Vec::new();
            let mut idx = vec![u32::MAX; 2 * tt * tt * (a + 1)];
            let mut off = 0usize;
            for c in 0..=b {
                for hl in 0..tt {
                    for hr in 0..tt {
                        let ph = (hl.count_ones() + hr.count_ones()) as usize;
                        for il in 0..=a {
                            if k < c + ph + il {
                                break;
                            }
                            let jl = k - c - ph - il;
                            if jl > a || (il, hl) > (jl, hr) {
                                continue;
                            }
                            let tri = (il, hl) == (jl, hr);
                            let ci = binom[a][il] as usize;
                            let cj = binom[a][jl] as usize;
                            let len = if tri { ci * (ci + 1) / 2 } else { ci * cj };
                            off = off.div_ceil(align) * align;
                            idx[((c * tt + hl) * tt + hr) * (a + 1) + il] = sbs.len() as u32;
                            sbs.push(SB { c: c as u8, hl: hl as u16, hr: hr as u16, il: il as u8, jl: jl as u8, tri, off, len });
                            off += len;
                        }
                    }
                }
            }
            shapes.push(SubShape { k, sbs, idx, len: off });
        }
        SubLayout { n, h, b, t, a, tt, binom, shapes }
    }

    /// Sub-block of layer `k` holding `(c, HL, HR, il, jl)` (any orientation).
    #[inline]
    pub fn find(&self, k: usize, c: usize, hl: usize, hr: usize, il: usize, jl: usize) -> Option<Ref> {
        if k > self.n {
            return None;
        }
        let (hl, hr, il, trans) = if (il, hl) <= (jl, hr) { (hl, hr, il, false) } else { (hr, hl, jl, true) };
        let v = self.shapes[k].idx[((c * self.tt + hl) * self.tt + hr) * (self.a + 1) + il];
        (v != u32::MAX).then_some(Ref { ix: v, trans })
    }

    /// Sub-blocks of layer `k-1` read by the pull into sub-block `s` of layer `k`.
    pub fn needs(&self, k: usize, s: &SB) -> Vec<u32> {
        let (c, hl, hr, il, jl) = (s.c as usize, s.hl as usize, s.hr as usize, s.il as usize, s.jl as usize);
        let mut v = vec![];
        let km = k - 1;
        if il > 0 {
            v.extend(self.find(km, c, hl, hr, il - 1, jl).map(|r| r.ix));
        }
        if jl > 0 {
            v.extend(self.find(km, c, hl, hr, il, jl - 1).map(|r| r.ix));
        }
        for x in 0..self.t {
            if hl >> x & 1 == 1 {
                v.extend(self.find(km, c, hl ^ 1 << x, hr, il, jl).map(|r| r.ix));
            }
            if hr >> x & 1 == 1 {
                v.extend(self.find(km, c, hl, hr ^ 1 << x, il, jl).map(|r| r.ix));
            }
        }
        if c == 1 {
            v.extend(self.find(km, 0, hl, hr, il, jl).map(|r| r.ix));
        }
        v.sort();
        v.dedup();
        v
    }

    /// The sub-block (of layer `N - k`) holding the complements of the sets of `s`.
    pub fn comp(&self, k: usize, s: &SB) -> Ref {
        let m = self.tt - 1;
        self.find(
            self.n - k,
            self.b - s.c as usize,
            !(s.hl as usize) & m,
            !(s.hr as usize) & m,
            self.a - s.il as usize,
            self.a - s.jl as usize,
        )
        .expect("complement sub-block")
    }

    /// Last layer that is computed (streamed, never stored): `h` for even `N`, `h+1` odd.
    pub fn klast(&self) -> usize {
        self.h + self.b
    }
}

/// One unit of work of the schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Job {
    /// compute and store sub-block `ix` of layer `k`
    Store { k: u8, ix: u32 },
    /// last layer: compute sub-block `ix` (and for even `N` its complement partner),
    /// combine, drop
    Final { ix: u32 },
}

pub struct Plan {
    pub jobs: Vec<Job>,
    /// after job `t`, free these `(layer, sub-block)`
    pub free_after: Vec<Vec<(u8, u32)>>,
    pub peak: usize,
    /// live words after each job (for the logs)
    pub live: Vec<usize>,
}

/// Node id: `base[k] + ix`.
struct Graph {
    base: Vec<usize>,
    size: Vec<usize>,
    layer: Vec<u8>,
    deps: Vec<Vec<u32>>,
    cons: Vec<Vec<u32>>,
    /// final jobs: id -> sub-block index in layer klast
    nfinal: usize,
}

fn graph(sl: &SubLayout) -> (Graph, Vec<u32>) {
    let kl = sl.klast();
    let mut base = vec![0usize; kl + 2];
    for k in 0..kl {
        base[k + 1] = base[k] + sl.shapes[k].sbs.len();
    }
    let nstored = base[kl];
    let mut size = vec![0usize; nstored];
    let mut layer = vec![0u8; nstored];
    let mut deps: Vec<Vec<u32>> = vec![vec![]; nstored];
    for k in 0..kl {
        for (ix, s) in sl.shapes[k].sbs.iter().enumerate() {
            let id = base[k] + ix;
            size[id] = s.len;
            layer[id] = k as u8;
            if k > 0 {
                deps[id] = sl.needs(k, s).into_iter().map(|p| (base[k - 1] + p as usize) as u32).collect();
            }
        }
    }
    // final jobs
    let mut fin = vec![];
    let sh = &sl.shapes[kl];
    for (ix, s) in sh.sbs.iter().enumerate() {
        let mut d: Vec<u32> = sl.needs(kl, s).into_iter().map(|p| (base[kl - 1] + p as usize) as u32).collect();
        if sl.b == 0 {
            let y = sl.comp(kl, s).ix;
            if (y as usize) < ix {
                continue; // the pair is handled once, at its smaller index
            }
            let ys = &sh.sbs[y as usize];
            d.extend(sl.needs(kl, ys).into_iter().map(|p| (base[kl - 1] + p as usize) as u32));
        } else {
            d.push((base[kl - 1] + sl.comp(kl, s).ix as usize) as u32);
        }
        d.sort();
        d.dedup();
        fin.push(ix as u32);
        deps.push(d);
        size.push(0);
        layer.push(kl as u8);
    }
    let nfinal = fin.len();
    let mut cons: Vec<Vec<u32>> = vec![vec![]; deps.len()];
    for (id, d) in deps.iter().enumerate() {
        for &p in d {
            cons[p as usize].push(id as u32);
        }
    }
    (Graph { base, size, layer, deps, cons, nfinal }, fin)
}

/// Greedy schedule.  `global = false`: layer by layer (only jobs of the lowest
/// unfinished layer are eligible); `global = true`: any ready job.  Among the eligible
/// jobs, take the one minimizing (words written) − (words freed right after it).
pub fn plan(sl: &SubLayout, global: bool) -> Plan {
    use std::collections::BTreeSet;
    let (g, fin) = graph(sl);
    let nn = g.deps.len();
    let mut rem: Vec<usize> = g.cons.iter().map(|c| c.len()).collect();
    let mut ndep: Vec<usize> = g.deps.iter().map(|d| d.len()).collect();
    let mut done = vec![false; nn];
    let heur: u32 = std::env::var("FOLDS_HEUR").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let net = |id: usize, rem: &[usize]| -> i64 {
        let mut x = g.size[id] as i64;
        for &p in &g.deps[id] {
            let r = rem[p as usize];
            if r == 1 {
                x -= g.size[p as usize] as i64;
            } else if heur & 1 == 1 {
                x -= (g.size[p as usize] / (4 * r)) as i64;
            }
        }
        x
    };
    // ready set keyed by (eligibility layer for layered mode, net, id)
    let key = |id: usize, rem: &[usize]| -> (u8, i64, u32) {
        let l = g.layer[id];
        let tie = if heur & 2 == 2 { 255 - l as u32 } else if heur & 4 == 4 { l as u32 } else { 0 };
        (if global { 0 } else { l }, net(id, rem), tie << 24 | id as u32)
    };
    let mut ready: BTreeSet<(u8, i64, u32)> = BTreeSet::new();
    let mut inkey: Vec<Option<(u8, i64, u32)>> = vec![None; nn];
    // layer 0 is given (the empty set), as a done node
    let mut live: usize = 0;
    let mut jobs = vec![];
    let mut free_after = vec![];
    let mut lives = vec![];
    let mut peak = 0usize;
    let mut complete = |id: usize,
                        done: &mut Vec<bool>,
                        ndep: &mut Vec<usize>,
                        ready: &mut BTreeSet<(u8, i64, u32)>,
                        inkey: &mut Vec<Option<(u8, i64, u32)>>,
                        rem: &Vec<usize>| {
        done[id] = true;
        for &q in &g.cons[id] {
            ndep[q as usize] -= 1;
            if ndep[q as usize] == 0 {
                let kq = key(q as usize, rem);
                ready.insert(kq);
                inkey[q as usize] = Some(kq);
            }
        }
    };
    live += g.size[0];
    complete(0, &mut done, &mut ndep, &mut ready, &mut inkey, &rem);
    while let Some(&kx) = ready.iter().next() {
        let id = (kx.2 & 0xFFFFFF) as usize;
        ready.remove(&kx);
        inkey[id] = None;
        peak = peak.max(live + g.size[id]);
        live += g.size[id];
        let mut freed = vec![];
        for &p in &g.deps[id] {
            let p = p as usize;
            rem[p] -= 1;
            if rem[p] == 0 {
                live -= g.size[p];
                let k = g.layer[p];
                freed.push((k, (p - g.base[k as usize]) as u32));
            } else if rem[p] == 1 {
                // its last reader now frees it: update that reader's key if ready
                for &q in &g.cons[p] {
                    let q = q as usize;
                    if let Some(old) = inkey[q] {
                        ready.remove(&old);
                        let nk = key(q, &rem);
                        ready.insert(nk);
                        inkey[q] = Some(nk);
                    }
                }
            }
        }
        if rem[id] == 0 && g.size[id] > 0 {
            // never read (cannot happen for a reachable layout, but keep the books right)
            live -= g.size[id];
            let k = g.layer[id];
            freed.push((k, (id - g.base[k as usize]) as u32));
        }
        if id >= g.base[sl.klast()] {
            jobs.push(Job::Final { ix: fin[id - g.base[sl.klast()]] });
        } else {
            let k = g.layer[id];
            jobs.push(Job::Store { k, ix: (id - g.base[k as usize]) as u32 });
        }
        free_after.push(freed);
        lives.push(live);
        complete(id, &mut done, &mut ndep, &mut ready, &mut inkey, &rem);
    }
    assert!(done.iter().all(|&d| d), "schedule incomplete");
    let _ = g.nfinal;
    Plan { jobs, free_after, peak, live: lives }
}

/// Split the stored sub-blocks between anonymous memory and the spill file, keeping
/// the anonymous total `≤ cap` words at all times.  First, for a target file peak
/// `F`, the times where the live total exceeds `F` are covered: at each such time,
/// live sub-blocks are moved to memory, those freed soonest first.  Then the rest go
/// to memory by increasing lifetime while they fit (less I/O).  The smallest feasible
/// `F` is found by bisection.  Returns `file[k][ix]`, the anonymous peak and the file
/// peak (words).
pub fn assign(sl: &SubLayout, p: &Plan, cap: usize) -> (Vec<Vec<bool>>, usize, usize) {
    let nj = p.jobs.len();
    let mut start: Vec<Vec<usize>> = sl.shapes.iter().map(|s| vec![usize::MAX; s.sbs.len()]).collect();
    let mut end: Vec<Vec<usize>> = sl.shapes.iter().map(|s| vec![nj; s.sbs.len()]).collect();
    for (t, j) in p.jobs.iter().enumerate() {
        if let Job::Store { k, ix } = *j {
            start[k as usize][ix as usize] = t;
        }
        for &(k, ix) in &p.free_after[t] {
            end[k as usize][ix as usize] = t;
        }
    }
    // items: (start, end, len, k, ix)
    let mut items: Vec<(usize, usize, usize, usize, usize)> = vec![];
    for k in 1..sl.klast() {
        for ix in 0..sl.shapes[k].sbs.len() {
            if start[k][ix] != usize::MAX {
                items.push((start[k][ix], end[k][ix], sl.shapes[k].sbs[ix].len, k, ix));
            }
        }
    }
    let mut total = vec![0usize; nj + 1];
    for &(a, b, len, _, _) in &items {
        total[a..=b].iter_mut().for_each(|x| *x += len);
    }
    let maxtot = *total.iter().max().unwrap_or(&0);
    // by start time, for the sweep
    let mut by_start: Vec<usize> = (0..items.len()).collect();
    by_start.sort_by_key(|&i| items[i].0);
    let mut by_life: Vec<usize> = (0..items.len()).collect();
    by_life.sort_by_key(|&i| (items[i].1 - items[i].0, i));
    let run = |target: usize| -> (Vec<bool>, usize, usize) {
        let mut inmem = vec![false; items.len()];
        let mut anon = vec![0usize; nj + 1];
        let fits = |anon: &[usize], it: &(usize, usize, usize, usize, usize)| anon[it.0..=it.1].iter().all(|&x| x + it.2 <= cap);
        // sweep: live candidates ordered by end time
        let mut heap = std::collections::BinaryHeap::new();
        let mut next = 0;
        for t in 0..=nj {
            while next < by_start.len() && items[by_start[next]].0 <= t {
                let i = by_start[next];
                heap.push(std::cmp::Reverse((items[i].1, i)));
                next += 1;
            }
            if total[t] <= target + anon[t] {
                continue;
            }
            let mut skipped = vec![];
            while total[t] > target + anon[t] {
                let Some(std::cmp::Reverse((e, i))) = heap.pop() else { break };
                if e < t || inmem[i] {
                    continue;
                }
                if fits(&anon, &items[i]) {
                    inmem[i] = true;
                    let it = items[i];
                    anon[it.0..=it.1].iter_mut().for_each(|x| *x += it.2);
                } else {
                    skipped.push(std::cmp::Reverse((e, i)));
                }
            }
            for x in skipped {
                heap.push(x);
            }
        }
        for &i in &by_life {
            if !inmem[i] && fits(&anon, &items[i]) {
                inmem[i] = true;
                let it = items[i];
                anon[it.0..=it.1].iter_mut().for_each(|x| *x += it.2);
            }
        }
        let fpeak = (0..=nj).map(|t| total[t] - anon[t]).max().unwrap_or(0);
        (inmem, *anon.iter().max().unwrap_or(&0), fpeak)
    };
    let mut best = run(maxtot);
    let (mut lo, mut hi) = (maxtot.saturating_sub(cap), best.2);
    while hi > lo + maxtot / 1000 {
        let mid = (lo + hi) / 2;
        let r = run(mid);
        if r.2 <= mid {
            hi = r.2.min(mid);
            if r.2 < best.2 {
                best = r;
            }
        } else {
            lo = mid + 1;
        }
    }
    let mut file: Vec<Vec<bool>> = sl.shapes.iter().map(|s| vec![true; s.sbs.len()]).collect();
    // layer 0 (one word) lives in memory
    file[0].iter_mut().for_each(|f| *f = false);
    for (i, it) in items.iter().enumerate() {
        file[it.3][it.4] = !best.0[i];
    }
    (file, best.1, best.2)
}

/// Total words written to the file region under `file`.
pub fn file_words(sl: &SubLayout, file: &[Vec<bool>]) -> usize {
    sl.shapes[..sl.klast()].iter().zip(file).map(|(sh, f)| sh.sbs.iter().zip(f).filter(|(_, b)| **b).map(|(s, _)| s.len).sum::<usize>()).sum()
}

// ---------------------------------------------------------------------------------
// Computation
// ---------------------------------------------------------------------------------

use crate::block::Region;
use crate::dp::{Ring, Word};
use crate::rule::Checker;
use rayon::prelude::*;
use std::time::Instant;

/// Colex tables of `a`-bit masks.
struct Tabs {
    /// `un[p]`: the masks of popcount `p`, increasing
    un: Vec<Vec<u32>>,
    rank: Vec<u32>,
    /// `rrem[p][v*p + q]`: rank of `un[p][v]` without its `q`-th lowest set bit
    rrem: Vec<Vec<u32>>,
}

fn tabs(a: usize) -> Tabs {
    let size = 1usize << a;
    let mut un: Vec<Vec<u32>> = vec![Vec::new(); a + 1];
    let mut rank = vec![0u32; size];
    for m in 0..size {
        let pc = (m as u32).count_ones() as usize;
        rank[m] = un[pc].len() as u32;
        un[pc].push(m as u32);
    }
    let rrem = un
        .iter()
        .map(|v| {
            let mut out = Vec::new();
            for &m in v {
                let mut bits = m;
                while bits != 0 {
                    let y = bits.trailing_zeros();
                    bits &= bits - 1;
                    out.push(rank[(m ^ (1 << y)) as usize]);
                }
            }
            out
        })
        .collect();
    Tabs { un, rank, rrem }
}

/// Read access to a stored sub-block in the orientation of the reader:
/// `at(u, v)` = the entry with left-low rank `u` and right-low rank `v`.
#[derive(Clone, Copy)]
struct Acc<W: Word> {
    p: *const W,
    su: usize,
    sv: usize,
    tri: bool,
}
unsafe impl<W: Word> Send for Acc<W> {}
unsafe impl<W: Word> Sync for Acc<W> {}

impl<W: Word> Acc<W> {
    #[inline(always)]
    fn ix(&self, u: usize, v: usize) -> usize {
        if self.tri {
            let (m, n) = if u >= v { (u, v) } else { (v, u) };
            m * (m + 1) / 2 + n
        } else {
            u * self.su + v * self.sv
        }
    }
    #[inline(always)]
    fn at(&self, u: usize, v: usize) -> u64 {
        unsafe { (*self.p.add(self.ix(u, v))).get64() }
    }
}

#[inline(always)]
fn mask(b: bool) -> u64 {
    (b as u64).wrapping_neg()
}

/// Everything a sub-block computation needs: its key, the panel masks of its rows and
/// columns, and accessors to the sub-blocks of the previous layer it pulls from.
struct Kern<'a, W: Word> {
    il: usize,
    jl: usize,
    n: usize,
    tri: bool,
    /// `rowm[u]` = panels of `Llo_u | HL | c`
    rowm: Vec<u64>,
    /// `colm[v]` = panels of `Rlo_v | HR`
    colm: Vec<u64>,
    /// low-left removal: `(il-1, jl)`
    pa: Option<Acc<W>>,
    /// low-right removal: `(il, jl-1)`
    pc: Option<Acc<W>>,
    /// high removals and the middle panel: (panel, sub-block), same `(u, v)`
    ph: Vec<(u32, Acc<W>)>,
    tb: &'a Tabs,
    chk: &'a Checker,
    ring: Ring,
    /// panels of `HL | c` and of `HR` (fixed for the sub-block)
    lhi: u64,
    rhi: u64,
    /// removing a low panel `x ≤ x0` (left: panel `x`; right: panel `N-1-x`) has a
    /// validity that depends only on its own side and the fixed panels: its window
    /// `(x, 2x]` (resp. its mirror) reaches the other side only in high panels
    x0: usize,
}

impl<W: Word> Kern<'_, W> {
    /// `g` of the set with left-low rank `u` (low removals `lx` = (panel, rank of
    /// `Llo` minus it)) and right-low rank `v` (removals `ry`, likewise).
    #[inline(always)]
    fn entry(&self, u: usize, v: usize, lx: &[(u32, u32)], ry: &[(u32, u32)]) -> W {
        let t = self.rowm[u] | self.colm[v];
        let chk = self.chk;
        let mut acc = 0u64;
        if let Some(pa) = &self.pa {
            for &(x, r) in lx {
                acc += pa.at(r as usize, v) & mask(chk.valid(t ^ (1u64 << x), x));
            }
        }
        if let Some(pc) = &self.pc {
            for &(y, r) in ry {
                acc += pc.at(u, r as usize) & mask(chk.valid(t ^ (1u64 << y), y));
            }
        }
        for &(p, ref ac) in &self.ph {
            acc += ac.at(u, v) & mask(chk.valid(t ^ (1u64 << p), p));
        }
        W::put(self.ring.red(acc as u128))
    }

    fn lrem(&self, u: usize, out: &mut [(u32, u32); 32]) -> usize {
        let l = self.tb.un[self.il][u];
        let mut bits = l;
        let mut q = 0;
        while bits != 0 {
            let x = bits.trailing_zeros();
            bits &= bits - 1;
            out[q] = (x, self.tb.rank[(l ^ (1 << x)) as usize]);
            q += 1;
        }
        q
    }

    fn rrem(&self, v: usize, out: &mut [(u32, u32); 32]) -> usize {
        let r = self.tb.un[self.jl][v];
        let rr = &self.tb.rrem[self.jl];
        let mut bits = r;
        let mut q = 0;
        while bits != 0 {
            let y = bits.trailing_zeros();
            bits &= bits - 1;
            out[q] = ((self.n - 1 - y as usize) as u32, rr[v * self.jl + q]);
            q += 1;
        }
        q
    }

    fn rows(&self) -> usize {
        if self.tri { self.colm.len() } else { self.rowm.len() }
    }

    /// Rows `[r0, r1)` into `out` (rect: rows `u` of `C(a,jl)` entries; triangle: rows
    /// `v`, columns `u ≤ v`; contiguous).
    fn tile(&self, r0: usize, r1: usize, out: &mut [W]) {
        let mut ry = [(0u32, 0u32); 32];
        if !self.tri {
            let mut lx = [[(0u32, 0u32); 32]; TILE];
            let mut nl = [0usize; TILE];
            let cj = self.colm.len();
            for q in 0..r1 - r0 {
                nl[q] = self.lrem(r0 + q, &mut lx[q]);
            }
            for v in 0..cj {
                let nr = self.rrem(v, &mut ry);
                for q in 0..r1 - r0 {
                    out[q * cj + v] = self.entry(r0 + q, v, &lx[q][..nl[q]], &ry[..nr]);
                }
            }
        } else {
            // rows v (rank Rlo), columns u <= v; walk u outer so that the reads of
            // pa at (rank(Llo\x), v) are consecutive in v
            let mut rys = [[(0u32, 0u32); 32]; TILE];
            let mut nrs = [0usize; TILE];
            for q in 0..r1 - r0 {
                nrs[q] = self.rrem(r0 + q, &mut rys[q]);
            }
            let base = r0 * (r0 + 1) / 2;
            let mut l1 = [(0u32, 0u32); 32];
            for u in 0..r1 {
                let n1 = self.lrem(u, &mut l1);
                for v in r0.max(u)..r1 {
                    let q = v - r0;
                    out[v * (v + 1) / 2 + u - base] = self.entry(u, v, &l1[..n1], &rys[q][..nrs[q]]);
                }
            }
        }
    }

    /// Rows `[r0, r1)` of a rectangular sub-block (as `tile`), for words of at most 16
    /// bits.  The left-low removals of `x ≤ x0` are valid or not for a whole row, so
    /// they are added row by row (a vectorized `u32` add of a row of `pa`); the
    /// right-low removals of `y ≤ x0` are valid or not for a whole column, so only the
    /// valid ones are read; the remaining terms are tested entry by entry.
    fn tile_fast(&self, r0: usize, r1: usize, out: &mut [W], acc: &mut Vec<u32>) {
        let nr = r1 - r0;
        let cj = self.colm.len();
        let chk = self.chk;
        let tb = self.tb;
        let x0 = self.x0 as u32;
        acc.clear();
        acc.resize(nr * cj, 0);
        let mut lxd = [[(0u32, 0u32); 32]; TILE];
        let mut nd = [0usize; TILE];
        for q in 0..nr {
            let u = r0 + q;
            let l = tb.un[self.il][u];
            let tr = self.rowm[u] | self.rhi;
            let mut bits = l;
            while bits != 0 {
                let x = bits.trailing_zeros();
                bits &= bits - 1;
                let r = tb.rank[(l ^ (1 << x)) as usize] as usize;
                if x <= x0 {
                    if chk.valid(tr ^ (1u64 << x), x) {
                        let pa = self.pa.as_ref().unwrap();
                        debug_assert!(!pa.tri && pa.sv == 1);
                        let row = unsafe { std::slice::from_raw_parts(pa.p.add(r * pa.su), cj) };
                        for (a, b) in acc[q * cj..(q + 1) * cj].iter_mut().zip(row) {
                            *a += b.get64() as u32;
                        }
                    }
                } else {
                    lxd[q][nd[q]] = (x, r as u32);
                    nd[q] += 1;
                }
            }
        }
        let rr = &tb.rrem[self.jl];
        let mut ryc = [0u32; 32];
        let mut ryd = [(0u32, 0u32); 32];
        for v in 0..cj {
            let r = tb.un[self.jl][v];
            let tc = self.colm[v] | self.lhi;
            let (mut nc, mut ndd) = (0, 0);
            let mut bits = r;
            let mut qq = 0;
            while bits != 0 {
                let y = bits.trailing_zeros();
                bits &= bits - 1;
                let p = (self.n - 1 - y as usize) as u32;
                let rk = rr[v * self.jl + qq];
                qq += 1;
                if y <= x0 {
                    if chk.valid(tc ^ (1u64 << p), p) {
                        ryc[nc] = rk;
                        nc += 1;
                    }
                } else {
                    ryd[ndd] = (p, rk);
                    ndd += 1;
                }
            }
            let cm = self.colm[v];
            for q in 0..nr {
                let u = r0 + q;
                let t = self.rowm[u] | cm;
                let mut s = acc[q * cj + v] as u64;
                if let Some(pa) = &self.pa {
                    for &(x, r) in &lxd[q][..nd[q]] {
                        s += pa.at(r as usize, v) & mask(chk.valid(t ^ (1u64 << x), x));
                    }
                }
                if let Some(pc) = &self.pc {
                    for &rk in &ryc[..nc] {
                        s += pc.at(u, rk as usize);
                    }
                    for &(p, rk) in &ryd[..ndd] {
                        s += pc.at(u, rk as usize) & mask(chk.valid(t ^ (1u64 << p), p));
                    }
                }
                for &(p, ref ac) in &self.ph {
                    s += ac.at(u, v) & mask(chk.valid(t ^ (1u64 << p), p));
                }
                out[q * cj + v] = W::put(self.ring.red(s as u128));
            }
        }
    }

    /// Compute the whole sub-block into `out` (length = sub-block length), in parallel.
    fn run(&self, out: *mut W) {
        struct P<W>(*mut W);
        unsafe impl<W> Send for P<W> {}
        unsafe impl<W> Sync for P<W> {}
        let o = P(out);
        let rows = self.rows();
        let tiles: Vec<usize> = (0..rows).step_by(TILE).collect();
        let cj = self.colm.len();
        let tri = self.tri;
        let fast = !tri && W::BYTES <= 2 && std::env::var_os("FOLDS_SLOW").is_none();
        let go = |acc: &mut Vec<u32>, r0: usize| {
            let o = &o;
            let r1 = (r0 + TILE).min(rows);
            let (s, l) = if tri { (r0 * (r0 + 1) / 2, r1 * (r1 + 1) / 2 - r0 * (r0 + 1) / 2) } else { (r0 * cj, (r1 - r0) * cj) };
            let sl = unsafe { std::slice::from_raw_parts_mut(o.0.add(s), l) };
            if fast {
                self.tile_fast(r0, r1, sl, acc);
            } else {
                self.tile(r0, r1, sl);
            }
        };
        if tiles.len() == 1 {
            go(&mut Vec::new(), 0);
        } else {
            tiles.into_par_iter().for_each_init(Vec::new, go);
        }
    }
}

/// Rows per tile.
const TILE: usize = 16;

/// Panels of an `R`-side mask (bit `q` = panel `N-1-q`).
#[inline]
fn rpanels(n: usize, r: u64) -> u64 {
    if r == 0 { 0 } else { r.reverse_bits() >> (64 - n) }
}

struct Mem<W: Word> {
    /// per layer: (anonymous, file) regions, created on first use
    reg: Vec<[Option<Region<W>>; 2]>,
    /// per layer, per sub-block: stored in the file region
    file: Vec<Vec<bool>>,
    /// per layer: number of sub-blocks still live (the regions are dropped at 0)
    live: Vec<usize>,
}

impl<W: Word> Mem<W> {
    fn ptr(&self, sl: &SubLayout, k: usize, ix: usize) -> *mut W {
        let r = self.region(k, ix);
        unsafe { r.ptr().add(sl.shapes[k].sbs[ix].off) }
    }
    fn region(&self, k: usize, ix: usize) -> &Region<W> {
        self.reg[k][self.file[k][ix] as usize].as_ref().expect("region")
    }
}

fn acc_of<W: Word>(sl: &SubLayout, k: usize, r: Ref, p: *const W) -> Acc<W> {
    let s = &sl.shapes[k].sbs[r.ix as usize];
    let w = sl.binom[sl.a][s.jl as usize] as usize;
    let (su, sv) = if r.trans { (1, w) } else { (w, 1) };
    Acc { p, su, sv, tri: s.tri }
}

/// Set up the computation of sub-block `s` of layer `k` (reads from layer `k-1`).
fn kern<'a, W: Word>(sl: &SubLayout, tb: &'a Tabs, chk: &'a Checker, ring: Ring, k: usize, s: &SB, pre: &dyn Fn(Ref) -> *const W) -> Kern<'a, W> {
    let (n, h, a) = (sl.n, sl.h, sl.a);
    let (c, hl, hr, il, jl) = (s.c as usize, s.hl as usize, s.hr as usize, s.il as usize, s.jl as usize);
    let km = k - 1;
    let lhi = (hl as u64) << a | (c as u64) << h;
    let rhi = rpanels(n, (hr as u64) << a);
    let rowm = tb.un[il].iter().map(|&l| l as u64 | lhi).collect();
    let colm = tb.un[jl].iter().map(|&r| rpanels(n, r as u64) | rhi).collect();
    let get = |c2: usize, hl2: usize, hr2: usize, il2: usize, jl2: usize| -> Acc<W> {
        let r = sl.find(km, c2, hl2, hr2, il2, jl2).expect("predecessor sub-block");
        acc_of(sl, km, r, pre(r))
    };
    let pa = (il > 0).then(|| get(c, hl, hr, il - 1, jl));
    let pc = (jl > 0).then(|| get(c, hl, hr, il, jl - 1));
    let mut ph = vec![];
    for x in 0..sl.t {
        if hl >> x & 1 == 1 {
            ph.push(((a + x) as u32, get(c, hl ^ 1 << x, hr, il, jl)));
        }
        if hr >> x & 1 == 1 {
            ph.push(((n - 1 - a - x) as u32, get(c, hl, hr ^ 1 << x, il, jl)));
        }
    }
    if c == 1 {
        ph.push((h as u32, get(0, hl, hr, il, jl)));
    }
    let x0 = (n - 1 - a) / 2;
    Kern { il, jl, n, tri: s.tri, rowm, colm, pa, pc, ph, tb, chk, ring, lhi, rhi, x0 }
}

/// `Σ w(e) gX(e) gY(comp e)` over the entries `e` of `x` (key `s`), where `y` reads the
/// complement sub-block in the reader's orientation.  `w` = orbit size.
fn pair_sum<W: Word>(sl: &SubLayout, ring: Ring, s: &SB, x: &[W], y: &Acc<W>) -> u128 {
    let (ci, cj) = (sl.binom[sl.a][s.il as usize] as usize, sl.binom[sl.a][s.jl as usize] as usize);
    let md = |v: u128| ring.red_any(v);
    let rows = |r: std::ops::Range<usize>| -> u128 {
        let mut tot = 0u128;
        for a in r {
            let mut t = 0u128;
            if s.tri {
                let v = a;
                for u in 0..=v {
                    let g = x[v * (v + 1) / 2 + u].get();
                    let f = y.at(ci - 1 - u, ci - 1 - v) as u128;
                    t += if u == v { 1 } else { 2 } * g * f;
                }
            } else {
                let u = a;
                for v in 0..cj {
                    let g = x[u * cj + v].get();
                    let f = y.at(ci - 1 - u, cj - 1 - v) as u128;
                    t += 2 * g * f;
                }
            }
            tot = md(tot + md(t));
        }
        tot
    };
    if ci <= 64 {
        rows(0..ci)
    } else {
        (0..ci).into_par_iter().step_by(16).map(|r0| rows(r0..(r0 + 16).min(ci))).reduce(|| 0, |p, q| md(p + q))
    }
}

/// A `kB` field of `/proc/self/status`.
fn rss_kb(field: &str) -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with(field)).and_then(|l| l.split_whitespace().nth(1)?.parse().ok()))
        .unwrap_or(0)
}

/// Memory guard for a shared memory cgroup (v1): before a job that grows our
/// anonymous memory by `grow` bytes, wait while `total_rss` of our cgroup (all
/// anonymous memory of all processes in it) + `grow` + `FOLDS_HEADROOM` GB (default
/// 1.5) exceeds the cgroup limit.  Page cache (the spill file) is not counted: the
/// kernel can write it back and drop it.
///
/// Also, before writing `w` bytes to the spill file, wait while the free disk space
/// there is below `w` + `FOLDS_DISK_MIN` GB (default 2): a full disk would kill the
/// process (`SIGBUS` on a write fault of the file mapping).
struct Guard {
    stat: Option<std::path::PathBuf>,
    limit: u64,
    headroom: u64,
    waited: f64,
    disk: Option<std::ffi::CString>,
    disk_min: u64,
}

unsafe extern "C" {
    fn statfs(path: *const std::ffi::c_char, buf: *mut [i64; 15]) -> i32;
}

fn disk_free(path: &std::ffi::CStr) -> Option<u64> {
    let mut b = [0i64; 15];
    // x86_64 struct statfs: f_type, f_bsize, f_blocks, f_bfree, f_bavail, ...
    (unsafe { statfs(path.as_ptr(), &mut b) } == 0).then(|| b[1] as u64 * b[4] as u64)
}

impl Guard {
    fn new() -> Self {
        let cg = std::fs::read_to_string("/proc/self/cgroup").ok().and_then(|s| {
            s.lines().find_map(|l| {
                let mut it = l.splitn(3, ':');
                let (_, ctl, path) = (it.next()?, it.next()?, it.next()?);
                (ctl == "memory").then(|| std::path::PathBuf::from(format!("/sys/fs/cgroup/memory{path}")))
            })
        });
        let limit = cg
            .as_ref()
            .and_then(|d| std::fs::read_to_string(d.join("memory.limit_in_bytes")).ok())
            .and_then(|v| v.trim().parse::<u64>().ok())
            .unwrap_or(u64::MAX);
        let headroom = (std::env::var("FOLDS_HEADROOM").ok().and_then(|v| v.parse::<f64>().ok()).unwrap_or(1.5) * 1e9) as u64;
        let stat = cg.map(|d| d.join("memory.stat")).filter(|_| limit < 1 << 50);
        let disk = std::env::var_os("FOLDS_SPILL").and_then(|d| std::ffi::CString::new(d.into_encoded_bytes()).ok());
        let disk_min = (std::env::var("FOLDS_DISK_MIN").ok().and_then(|v| v.parse::<f64>().ok()).unwrap_or(2.0) * 1e9) as u64;
        Guard { stat, limit, headroom, waited: 0.0, disk, disk_min }
    }
    fn wait_disk(&mut self, w: u64) {
        let Some(d) = self.disk.clone() else { return };
        let t = Instant::now();
        let mut warned = false;
        while let Some(f) = disk_free(&d) {
            if f >= w + self.disk_min {
                break;
            }
            if !warned {
                eprintln!("  guard: free disk {:.2} GB < {:.2} GB + {:.2} GB, waiting", f as f64 / 1e9, w as f64 / 1e9, self.disk_min as f64 / 1e9);
                warned = true;
            }
            std::thread::sleep(std::time::Duration::from_secs(5));
        }
        if warned {
            self.waited += t.elapsed().as_secs_f64();
            eprintln!("  guard: resumed after {:.0}s", t.elapsed().as_secs_f64());
        }
    }
    fn anon(&self) -> Option<u64> {
        let s = std::fs::read_to_string(self.stat.as_ref()?).ok()?;
        s.lines().find(|l| l.starts_with("total_rss ")).and_then(|l| l.split_whitespace().nth(1)?.parse().ok())
    }
    fn wait(&mut self, grow: u64) {
        let mut warned = false;
        let t = Instant::now();
        while let Some(a) = self.anon() {
            if a + grow + self.headroom <= self.limit {
                break;
            }
            if !warned {
                eprintln!(
                    "  guard: cgroup anonymous {:.2} GB + {:.2} GB + headroom {:.2} GB > limit {:.2} GB, waiting",
                    a as f64 / 1e9,
                    grow as f64 / 1e9,
                    self.headroom as f64 / 1e9,
                    self.limit as f64 / 1e9
                );
                warned = true;
            }
            std::thread::sleep(std::time::Duration::from_secs(5));
        }
        if warned {
            self.waited += t.elapsed().as_secs_f64();
            eprintln!("  guard: resumed after {:.0}s", t.elapsed().as_secs_f64());
        }
    }
}

/// Words per page for `W`.
fn page_words<W: Word>() -> usize {
    4096 / W::BYTES
}

/// The sub-block count: same result as `block::count`, with the schedule of `plan`
/// and the memory split of `assign` (`FOLDS_ANON` = anonymous cap in GB when
/// `FOLDS_SPILL` is set; everything is anonymous otherwise).
pub fn count<W: Word>(n: usize, t: usize, chk: &Checker, ring: Ring, verbose: bool) -> u128 {
    assert!(W::BYTES <= 8, "sub-block kernels accumulate in u64");
    if n <= 1 {
        return 1;
    }
    let t0 = Instant::now();
    let t = t.min(n / 2);
    let sl = SubLayout::aligned(n, t, page_words::<W>());
    let tb = tabs(sl.a);
    let plan = plan(&sl, true);
    let spill = std::env::var_os("FOLDS_SPILL").map(std::path::PathBuf::from);
    let cap_gb: f64 = std::env::var("FOLDS_ANON").ok().and_then(|v| v.parse().ok()).unwrap_or(7.0);
    let (file, apeak, fpeak) = if spill.is_some() {
        assign(&sl, &plan, (cap_gb * 1e9) as usize / W::BYTES)
    } else {
        (sl.shapes.iter().map(|s| vec![false; s.sbs.len()]).collect(), plan.peak, 0)
    };
    let kl = sl.klast();
    if verbose {
        eprintln!(
            "  sub-blocks t={} a={}: {} jobs, sim.peak {:.2} GB (anon {:.2} GB, file {:.2} GB, {:.1} GB written to file) plan {:.1}s",
            t,
            sl.a,
            plan.jobs.len(),
            (plan.peak * W::BYTES) as f64 / 1e9,
            (apeak * W::BYTES) as f64 / 1e9,
            (fpeak * W::BYTES) as f64 / 1e9,
            (file_words(&sl, &file) * W::BYTES) as f64 / 1e9,
            t0.elapsed().as_secs_f64()
        );
    }
    let mut live = vec![0usize; kl + 1];
    for j in &plan.jobs {
        if let Job::Store { k, .. } = j {
            live[*k as usize] += 1;
        }
    }
    let mut mem: Mem<W> = Mem { reg: (0..=kl).map(|_| [None, None]).collect(), file, live };
    // layer 0: the empty set, g = 1
    {
        let r: Region<W> = Region::with(1, None, false);
        unsafe { r.part(0, 1)[0] = W::put(1) };
        mem.reg[0][0] = Some(r);
        mem.live[0] = 1;
    }
    let mut total = 0u128;
    let nj = plan.jobs.len();
    let mut next_report = 0usize;
    let mut tmp_x: Vec<W> = vec![];
    let mut tmp_y: Vec<W> = vec![];
    let mut guard = Guard::new();
    for (tj, jb) in plan.jobs.iter().enumerate() {
        match *jb {
            Job::Store { k, ix } => {
                let (k, ix) = (k as usize, ix as usize);
                let s = sl.shapes[k].sbs[ix];
                let f = mem.file[k][ix];
                guard.wait(if f { 0 } else { (s.len * W::BYTES) as u64 } + (64 << 20));
                if f {
                    guard.wait_disk((s.len * W::BYTES) as u64);
                }
                if mem.reg[k][f as usize].is_none() {
                    let dir = if f { spill.as_deref() } else { None };
                    mem.reg[k][f as usize] = Some(Region::with(sl.shapes[k].len, dir, false));
                }
                // prefetch file-backed inputs
                for p in sl.needs(k, &s) {
                    let ps = &sl.shapes[k - 1].sbs[p as usize];
                    mem.region(k - 1, p as usize).prefetch(ps.off, ps.len);
                }
                let pre = |r: Ref| mem.ptr(&sl, k - 1, r.ix as usize) as *const W;
                let ke: Kern<W> = kern(&sl, &tb, chk, ring, k, &s, &pre);
                ke.run(mem.ptr(&sl, k, ix));
                if f {
                    mem.region(k, ix).flush_async(s.off, s.len);
                    mem.region(k, ix).unmap_pages(s.off, s.len);
                }
                for p in sl.needs(k, &s) {
                    let ps = &sl.shapes[k - 1].sbs[p as usize];
                    mem.region(k - 1, p as usize).unmap_pages(ps.off, ps.len);
                }
            }
            Job::Final { ix } => {
                let ix = ix as usize;
                let s = sl.shapes[kl].sbs[ix];
                guard.wait((2 * s.len * W::BYTES) as u64 + (64 << 20));
                let mut deps = sl.needs(kl, &s);
                let cr = sl.comp(kl, &s);
                if sl.b == 0 {
                    deps.extend(sl.needs(kl, &sl.shapes[kl].sbs[cr.ix as usize]));
                } else {
                    deps.push(cr.ix);
                }
                for &p in &deps {
                    let ps = &sl.shapes[kl - 1].sbs[p as usize];
                    mem.region(kl - 1, p as usize).prefetch(ps.off, ps.len);
                }
                let deps_all = deps;
                let pre = |r: Ref| mem.ptr(&sl, kl - 1, r.ix as usize) as *const W;
                tmp_x.clear();
                tmp_x.resize(s.len, W::default());
                kern::<W>(&sl, &tb, chk, ring, kl, &s, &pre).run(tmp_x.as_mut_ptr());
                let part = if sl.b == 0 {
                    // even N: the partner = the complement sub-block (same layer)
                    let same = cr.ix as usize == ix;
                    let py: *const W = if same {
                        tmp_x.as_ptr()
                    } else {
                        let ys = sl.shapes[kl].sbs[cr.ix as usize];
                        tmp_y.clear();
                        tmp_y.resize(ys.len, W::default());
                        kern::<W>(&sl, &tb, chk, ring, kl, &ys, &pre).run(tmp_y.as_mut_ptr());
                        tmp_y.as_ptr()
                    };
                    let y = acc_of(&sl, kl, cr, py);
                    let v = pair_sum(&sl, ring, &s, &tmp_x, &y);
                    if same { v } else { ring.red_any(2 * v) }
                } else {
                    // odd N: the complements lie in layer kl-1 (stored)
                    let y = acc_of(&sl, kl - 1, cr, mem.ptr(&sl, kl - 1, cr.ix as usize));
                    pair_sum(&sl, ring, &s, &tmp_x, &y)
                };
                total = ring.red_any(total + part);
                for p in deps_all {
                    let ps = &sl.shapes[kl - 1].sbs[p as usize];
                    mem.region(kl - 1, p as usize).unmap_pages(ps.off, ps.len);
                }
            }
        }
        for &(k, ix) in &plan.free_after[tj] {
            let (k, ix) = (k as usize, ix as usize);
            let s = &sl.shapes[k].sbs[ix];
            mem.region(k, ix).release(s.off, s.len);
            mem.live[k] -= 1;
            if mem.live[k] == 0 {
                mem.reg[k] = [None, None];
            }
        }
        if verbose && tj >= next_report {
            next_report += nj / 40 + 1;
            eprintln!(
                "  job {:6}/{}: {:?} sim.live {:.2} GB rss {:.2} GB (anon {:.2}, file {:.2}) rss.peak {:.2} GB t={:.1}s",
                tj,
                nj,
                jb,
                (plan.live[tj] * W::BYTES) as f64 / 1e9,
                rss_kb("VmRSS:") as f64 / 1e6,
                rss_kb("RssAnon:") as f64 / 1e6,
                rss_kb("RssFile:") as f64 / 1e6,
                crate::block::peak_rss() as f64 / 1e9,
                t0.elapsed().as_secs_f64()
            );
        }
    }
    if verbose {
        eprintln!(
            "  sub-block count done: rss.peak {:.2} GB t={:.1}s (guard waits {:.0}s)",
            crate::block::peak_rss() as f64 / 1e9,
            t0.elapsed().as_secs_f64(),
            guard.waited
        );
    }
    total
}
