//! Step validity.  Panels are 0-indexed bit positions `p = m - 1` of a `u64` mask `S`
//! (the set of panels bisected before the step).  The window radius is
//! `r = min(p, N-1-p)`.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rule {
    /// `#{d<=r : p-d in S} = #{d<=r : p+d in S}`
    Semi,
    /// `p-d in S <=> p+d in S` for all `d <= r` (OEIS A003407)
    Sym,
}

impl Rule {
    pub fn name(self) -> &'static str {
        match self {
            Rule::Semi => "semi",
            Rule::Sym => "sym",
        }
    }
    pub fn parse(s: &str) -> Option<Rule> {
        match s {
            "semi" => Some(Rule::Semi),
            "sym" => Some(Rule::Sym),
            _ => None,
        }
    }
}

/// Precomputed window masks for a fixed `N`.
#[derive(Clone)]
pub struct Checker {
    pub n: usize,
    pub rule: Rule,
    lm: [u64; 64],
    rm: [u64; 64],
}

impl Checker {
    pub fn new(n: usize, rule: Rule) -> Self {
        assert!(n >= 1 && n <= 63);
        let mut lm = [0u64; 64];
        let mut rm = [0u64; 64];
        for p in 0..n {
            let r = p.min(n - 1 - p);
            for d in 1..=r {
                lm[p] |= 1u64 << (p - d);
                rm[p] |= 1u64 << (p + d);
            }
        }
        Checker { n, rule, lm, rm }
    }

    /// Is bisecting panel `p` (not in `s`) valid when `s` is already bisected?
    #[inline(always)]
    pub fn valid(&self, s: u64, p: u32) -> bool {
        let p = p as usize;
        match self.rule {
            Rule::Semi => (s & self.lm[p]).count_ones() == (s & self.rm[p]).count_ones(),
            Rule::Sym => {
                // reverse_bits sends bit p-d to 63-p+d; align it with bit p+d.
                let rv = s.reverse_bits();
                let sh = if p <= 31 { rv >> (63 - 2 * p) } else { rv << (2 * p - 63) };
                ((s ^ sh) & self.rm[p]) == 0
            }
        }
    }

    /// The definition, written out literally (for testing).
    pub fn valid_slow(&self, s: u64, p: u32) -> bool {
        let p = p as i64;
        let n = self.n as i64;
        let r = p.min(n - 1 - p);
        let inn = |q: i64| (s >> q) & 1 == 1;
        match self.rule {
            Rule::Semi => {
                let l = (1..=r).filter(|&d| inn(p - d)).count();
                let rr = (1..=r).filter(|&d| inn(p + d)).count();
                l == rr
            }
            Rule::Sym => (1..=r).all(|d| inn(p - d) == inn(p + d)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fast_matches_slow() {
        for n in 1..=12 {
            for rule in [Rule::Semi, Rule::Sym] {
                let c = Checker::new(n, rule);
                for s in 0u64..(1 << n) {
                    for p in 0..n as u32 {
                        if s >> p & 1 == 0 {
                            assert_eq!(c.valid(s, p), c.valid_slow(s, p), "n={n} s={s:b} p={p}");
                        }
                    }
                }
            }
        }
        // large n spot check for the shift branch p > 31
        let c = Checker::new(63, Rule::Sym);
        let mut x = 0x9E3779B97F4A7C15u64;
        for _ in 0..100000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let s = x & ((1u64 << 63) - 1);
            for p in 0..63u32 {
                if s >> p & 1 == 0 {
                    assert_eq!(c.valid(s, p), c.valid_slow(s, p));
                }
            }
        }
    }
}
