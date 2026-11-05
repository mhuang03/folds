mod brute;
mod dp;
mod layout;
mod rule;
mod stats;

use rule::{Checker, Rule};
use std::time::Instant;

pub const SEMI_KNOWN: [u128; 27] = [
    1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908, 47821296,
    276182312, 1481994716, 10084180418, 55082188120, 398874108930, 2505681033958,
    18168130281086, 119006527671252, 979730153850974, 6564449510287388, 55581983250573500,
    413109755332919448,
];
/// OEIS A003407
pub const SYM_KNOWN: [u128; 14] =
    [1, 2, 4, 10, 20, 48, 104, 282, 496, 1066, 2460, 6128, 12840, 29380];

fn known(rule: Rule, n: usize) -> Option<u128> {
    let t: &[u128] = match rule {
        Rule::Semi => &SEMI_KNOWN,
        Rule::Sym => &SYM_KNOWN,
    };
    t.get(n - 1).copied()
}

/// Moduli for the low-memory CRT modes (pairwise coprime).
const MOD32: [u64; 4] = [1 << 32, 4294967291, 4294967279, 4294967231];
const MOD16: [u64; 8] = [1 << 16, 65521, 65519, 65497, 65479, 65449, 65447, 65437];

fn inv_mod(a: u64, m: u64) -> u64 {
    let (mut t, mut nt, mut r, mut nr) = (0i128, 1i128, m as i128, (a % m) as i128);
    while nr != 0 {
        let q = r / nr;
        (t, nt) = (nt, t - q * nt);
        (r, nr) = (nr, r - q * nr);
    }
    assert_eq!(r, 1);
    t.rem_euclid(m as i128) as u64
}

/// Garner reconstruction of `x mod Π m_i` (the product must stay below 2^128).
fn crt(res: &[u64], mods: &[u64]) -> u128 {
    let mut x: u128 = 0;
    let mut prod: u128 = 1;
    for (&r, &m) in res.iter().zip(mods) {
        let mm = m as u128;
        let t = ((r as u128 + mm - x % mm) % mm) * inv_mod((prod % mm) as u64, m) as u128 % mm;
        x += prod * t;
        prod = prod.checked_mul(mm).expect("CRT modulus product overflows u128");
    }
    x
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Mode {
    Exact,
    /// `u32` residues, number of moduli
    M32(usize),
    /// `u16` residues, number of moduli
    M16(usize),
}

fn count(n: usize, rule: Rule, mode: Mode, verbose: bool) -> (u128, f64) {
    let chk = Checker::new(n, rule);
    let t = Instant::now();
    let v = match mode {
        Mode::Exact => {
            assert!(n <= 41, "u64 exactness needs N <= 41");
            dp::count::<u64>(n, &chk, dp::Ring { modulus: 0 }, verbose)
        }
        Mode::M32(q) | Mode::M16(q) => {
            let mods: &[u64] = if let Mode::M32(_) = mode { &MOD32[..q] } else { &MOD16[..q] };
            let mut res = vec![];
            for &m in mods {
                let ring = dp::Ring { modulus: m };
                let r = if let Mode::M32(_) = mode {
                    dp::count::<u32>(n, &chk, ring, verbose)
                } else {
                    dp::count::<u16>(n, &chk, ring, verbose)
                } as u64;
                res.push(r);
                if verbose {
                    eprintln!("  N={} residue mod {} = {} ({:.1}s)", n, m, r, t.elapsed().as_secs_f64());
                }
            }
            crt(&res, mods)
        }
    };
    (v, t.elapsed().as_secs_f64())
}

fn usage() -> ! {
    eprintln!(
        "usage:
  folds <semi|sym> A [B] [--mod] [--threads T] [-v]   count a(N) for N = A..B
  folds stats <semi|sym> N [--threads T]               refined statistics (full forward DP)
  folds check                                          validate against brute force and known terms
options:
  --mod32 Q   store u32 residues (1/2 the memory), Q runs + CRT (exact below 2^(32Q)), Q<=4
  --mod16 Q   store u16 residues (1/4 the memory), Q runs + CRT (exact below 2^(16Q)), Q<=7
  --threads   worker threads (default 3)"
    );
    std::process::exit(2)
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut threads = 3usize;
    let mut mode = Mode::Exact;
    let mut verbose = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--threads" => {
                threads = args[i + 1].parse().unwrap();
                args.drain(i..i + 2);
            }
            "--mod32" => {
                mode = Mode::M32(args[i + 1].parse().unwrap());
                args.drain(i..i + 2);
            }
            "--mod16" => {
                mode = Mode::M16(args[i + 1].parse().unwrap());
                args.drain(i..i + 2);
            }
            "-v" => {
                verbose = true;
                args.remove(i);
            }
            _ => i += 1,
        }
    }
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    if args.is_empty() {
        usage();
    }
    match args[0].as_str() {
        "check" => check(),
        "stats" => {
            if args.len() < 3 {
                usage();
            }
            let rule = Rule::parse(&args[1]).unwrap_or_else(|| usage());
            let n: usize = args[2].parse().unwrap();
            stats::run(n, rule);
        }
        r => {
            let rule = Rule::parse(r).unwrap_or_else(|| usage());
            let a: usize = args.get(1).unwrap_or_else(|| usage()).parse().unwrap();
            let b: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(a);
            for n in a..=b {
                let (v, secs) = count(n, rule, mode, verbose);
                let tag = match known(rule, n) {
                    Some(k) if k == v => "  (matches known)",
                    Some(_) => "  MISMATCH WITH KNOWN VALUE",
                    None => "",
                };
                println!("{} {} {:.3}s{}", n, v, secs, tag);
            }
        }
    }
}

fn check() {
    use brute::*;
    let mut ok = true;
    for rule in [Rule::Semi, Rule::Sym] {
        for n in 1..=24usize {
            let chk = Checker::new(n, rule);
            let mut vals = vec![];
            if n <= 9 {
                vals.push(("perm", by_permutations(&chk)));
            }
            if n <= 20 {
                let g = brute::subset_dp(&chk);
                vals.push(("subset", g[(1usize << n) - 1]));
            }
            vals.push(("mitm64", dp::count::<u64>(n, &chk, dp::Ring { modulus: 0 }, false)));
            if n <= 18 {
                vals.push(("crt32", count(n, rule, Mode::M32(3), false).0));
                vals.push(("crt16", count(n, rule, Mode::M16(6), false).0));
            }
            if let Some(k) = known(rule, n) {
                vals.push(("known", k));
            }
            let all = vals.iter().all(|v| v.1 == vals[0].1);
            ok &= all;
            println!("{} N={:2} {} {}", rule.name(), n, if all { "ok " } else { "BAD" }, vals.iter().map(|(a, b)| format!("{a}={b}")).collect::<Vec<_>>().join(" "));
        }
    }
    // stats consistency: by-first (brute) == by-last (stats) for small N
    for n in 1..=12usize {
        let chk = Checker::new(n, Rule::Semi);
        let g = brute::subset_dp(&chk);
        let full = (1usize << n) - 1;
        let st = stats::compute(n, Rule::Semi);
        for m in 0..n {
            ok &= st.by_last[m] == g[full ^ (1 << m)];
        }
        for k in 0..=n {
            let pk: u128 = (0..=full).filter(|s| s.count_ones() as usize == k).map(|s| g[s]).sum();
            ok &= st.prefixes[k] == pk;
        }
    }
    println!("{}", if ok { "ALL OK" } else { "FAILURES" });
    if !ok {
        std::process::exit(1);
    }
}
