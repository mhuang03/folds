//! Refined statistics from the full forward DP (all layers `0..=N`, `u128` words,
//! mirror-reduced, two layers in memory at a time).
//!
//! * `prefixes[k]` = `Σ_{|S|=k} g(S)`, the number of valid prefixes of length `k`
//! * `reach[k]`    = number of `k`-sets `S` with `g(S) > 0`
//! * `dead[k]`     = number of `k`-sets with `g(S) > 0` and no valid next step
//! * `by_last[m]`  = `g([N] \ m)` = #sequences ending in `m` (the last step is always
//!   valid) = #sequences starting with `m` (reversal)
//! * `by_last2[x][m]` = #sequences ending `.., x, m` = `g([N]\{x,m})·[([N]\{x,m}, x) valid]`
//!   = #sequences starting `m, x, ..`

use crate::dp::{self, Layer, Ring};
use crate::layout::{entry, Layout};
use crate::rule::{Checker, Rule};
use rayon::prelude::*;

pub struct Stats {
    pub n: usize,
    pub total: u128,
    pub prefixes: Vec<u128>,
    pub reach: Vec<u128>,
    pub dead: Vec<u128>,
    /// `doomed[k]` = #k-sets with `g(S) > 0` but `f(S) = g(S^c) = 0` (only for N <= 26)
    pub doomed: Vec<u128>,
    /// `alive[k]` = #k-sets with `g(S) > 0` and `f(S) > 0` (only for N <= 26)
    pub alive: Vec<u128>,
    pub by_last: Vec<u128>,
    pub by_last2: Vec<Vec<u128>>,
}

pub fn compute(n: usize, rule: Rule) -> Stats {
    let lay = Layout::new(n);
    let chk = Checker::new(n, rule);
    let ring = Ring { modulus: 0 };
    let full = lay.full();
    let mut st = Stats {
        n,
        total: 0,
        prefixes: vec![0; n + 1],
        reach: vec![0; n + 1],
        dead: vec![0; n + 1],
        doomed: vec![0; n + 1],
        alive: vec![0; n + 1],
        by_last: vec![0; n],
        by_last2: vec![vec![0; n]; n],
    };
    let mut cur: Layer<u128> = dp::layer0(&lay);
    let keep = n <= 26;
    let mut all: Vec<Layer<u128>> = Vec::new();
    for k in 0..=n {
        if k > 0 {
            let next = dp::step(&lay, &chk, ring, &cur);
            let old = std::mem::replace(&mut cur, next);
            if keep {
                all.push(old);
            }
        }
        st.prefixes[k] = dp::layer_sum(&lay, ring, &cur);
        let rows = cur.shape.rows(&lay);
        let (re, de) = rows
            .par_iter()
            .map(|&(bl, row, start, len)| {
                let (mut re, mut de) = (0u128, 0u128);
                for col in 0..len {
                    if cur.data[start + col] == 0 {
                        continue;
                    }
                    let w = dp::weight(&bl, row, col) as u128;
                    re += w;
                    let (l, r) = entry(&lay, &bl, row, col);
                    let s = lay.compose(l, bl.c, r);
                    let mut free = full ^ s;
                    let mut any = false;
                    while free != 0 {
                        let p = free.trailing_zeros();
                        free &= free - 1;
                        if chk.valid(s, p) {
                            any = true;
                            break;
                        }
                    }
                    if !any && k < n {
                        de += w;
                    }
                }
                (re, de)
            })
            .reduce(|| (0, 0), |a, b| (a.0 + b.0, a.1 + b.1));
        st.reach[k] = re;
        st.dead[k] = de;
        if k + 2 == n {
            for x in 0..n {
                for m in 0..n {
                    if x != m {
                        let s = full ^ (1u64 << x) ^ (1u64 << m);
                        if chk.valid(s, x as u32) {
                            st.by_last2[x][m] = cur.at(&lay, s);
                        }
                    }
                }
            }
        }
        if k + 1 == n {
            for m in 0..n {
                st.by_last[m] = cur.at(&lay, full ^ (1u64 << m));
            }
        }
        if k == n {
            st.total = cur.data[0];
        }
    }
    if keep {
        all.push(cur);
        for k in 0..=n {
            let (lk, lc) = (&all[k], &all[n - k]);
            let rows = lk.shape.rows(&lay);
            let (dm, al) = rows
                .par_iter()
                .map(|&(bl, row, start, len)| {
                    let (mut dm, mut al) = (0u128, 0u128);
                    for col in 0..len {
                        if lk.data[start + col] == 0 {
                            continue;
                        }
                        let w = dp::weight(&bl, row, col) as u128;
                        let (l, r) = entry(&lay, &bl, row, col);
                        let s = lay.compose(l, bl.c, r);
                        if lc.at(&lay, full ^ s) == 0 { dm += w } else { al += w }
                    }
                    (dm, al)
                })
                .reduce(|| (0, 0), |a, b| (a.0 + b.0, a.1 + b.1));
            st.doomed[k] = dm;
            st.alive[k] = al;
        }
    }
    st
}

pub fn run(n: usize, rule: Rule) {
    let t = std::time::Instant::now();
    let st = compute(n, rule);
    let j = |v: &[u128]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
    println!("# {} N={} ({:.2}s)", rule.name(), n, t.elapsed().as_secs_f64());
    println!("total {}", st.total);
    println!("prefixes(k=0..N) {}", j(&st.prefixes));
    println!("reachable_sets(k=0..N) {}", j(&st.reach));
    println!("dead_end_sets(k=0..N) {}", j(&st.dead));
    println!("dead_end_total {}", st.dead.iter().sum::<u128>());
    if n <= 26 {
        println!("alive_sets(k=0..N) {}", j(&st.alive));
        println!("doomed_sets(k=0..N) {}", j(&st.doomed));
        println!("doomed_total {}", st.doomed.iter().sum::<u128>());
    }
    println!("by_first=by_last(m=1..N) {}", j(&st.by_last));
    println!("by_first2[m][x] = #seq starting m,x (rows m=1..N):");
    for m in 0..n {
        let row: Vec<u128> = (0..n).map(|x| st.by_last2[x][m]).collect();
        println!("  {}", j(&row));
    }
    let _ = st.n;
}
