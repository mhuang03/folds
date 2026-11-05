//! Reference implementations (slow, simple).

use crate::rule::Checker;

/// Enumerate all permutations directly from the definition.  `N <= 10`.
pub fn by_permutations(c: &Checker) -> u128 {
    fn rec(c: &Checker, s: u64, left: usize) -> u128 {
        if left == 0 {
            return 1;
        }
        let mut t = 0;
        for p in 0..c.n as u32 {
            if s >> p & 1 == 0 && c.valid_slow(s, p) {
                t += rec(c, s | 1 << p, left - 1);
            }
        }
        t
    }
    rec(c, 0, c.n)
}

/// Plain `2^N` subset DP (same as `experiments/semi.c`).  Returns the whole table `g`.
pub fn subset_dp(c: &Checker) -> Vec<u128> {
    let n = c.n;
    let full = (1u64 << n) - 1;
    let mut g = vec![0u128; 1 << n];
    g[0] = 1;
    for s in 0..full {
        let v = g[s as usize];
        if v == 0 {
            continue;
        }
        let mut free = full & !s;
        while free != 0 {
            let p = free.trailing_zeros();
            free &= free - 1;
            if c.valid(s, p) {
                g[(s | 1 << p) as usize] += v;
            }
        }
    }
    g
}
