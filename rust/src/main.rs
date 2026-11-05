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

/// Moduli for the low-memory CRT mode (pairwise coprime, all ≤ 2^32).
const MODULI: [u64; 4] = [1 << 32, 4294967291, 4294967279, 4294967231];

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

/// Garner reconstruction from residues mod MODULI[0..3]; result < 2^96.
fn crt3(r: &[u64; 3]) -> u128 {
    let m = &MODULI;
    let (m0, m1, m2) = (m[0] as u128, m[1] as u128, m[2] as u128);
    let x0 = r[0] as u128;
    // x = x0 + m0*t1 + m0*m1*t2
    let t1 = ((r[1] as u128 + m1 - x0 % m1) % m1) * inv_mod(m[0] % m[1], m[1]) as u128 % m1;
    let x01 = x0 + m0 * t1; // < m0*m1
    let inv01 = inv_mod(((m0 * m1) % m2) as u64, m[2]) as u128;
    let t2 = ((r[2] as u128 + m2 - x01 % m2) % m2) * inv01 % m2;
    x01 + m0 * m1 * t2
}

fn count(n: usize, rule: Rule, modmode: bool, verbose: bool) -> (u128, f64) {
    let chk = Checker::new(n, rule);
    let t = Instant::now();
    let v = if !modmode {
        assert!(n <= 41, "u64 exactness needs N <= 41");
        dp::count::<u64>(n, &chk, dp::Ring { modulus: 0 }, verbose)
    } else {
        let mut r = [0u64; 3];
        for (q, ri) in r.iter_mut().enumerate() {
            *ri = dp::count::<u32>(n, &chk, dp::Ring { modulus: MODULI[q] }, verbose) as u64;
            if verbose {
                eprintln!("  residue mod {} = {} ({:.1}s)", MODULI[q], ri, t.elapsed().as_secs_f64());
            }
        }
        crt3(&r)
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
  --mod       store u32 residues (half the memory), 3 runs + CRT (exact below 2^96)
  --threads   worker threads (default 3)"
    );
    std::process::exit(2)
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut threads = 3usize;
    let mut modmode = false;
    let mut verbose = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--threads" => {
                threads = args[i + 1].parse().unwrap();
                args.drain(i..i + 2);
            }
            "--mod" => {
                modmode = true;
                args.remove(i);
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
                let (v, secs) = count(n, rule, modmode, verbose);
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
            if n <= 16 {
                let mut r = [0u64; 3];
                for q in 0..3 {
                    r[q] = dp::count::<u32>(n, &chk, dp::Ring { modulus: MODULI[q] }, false) as u64;
                }
                vals.push(("crt32", crt3(&r)));
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
