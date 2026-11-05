mod block;
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
const MOD8: [u64; 16] = [256, 251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193, 191, 181, 179, 173];

fn moduli(w: usize) -> &'static [u64] {
    match w {
        32 => &MOD32,
        16 => &MOD16,
        8 => &MOD8,
        _ => panic!("width must be 8, 16 or 32"),
    }
}

/// One residue (or the exact value for `w = 64`) with the chosen code path.
fn one(n: usize, chk: &Checker, w: usize, m: u64, blocks: bool, verbose: bool) -> u128 {
    let ring = dp::Ring { modulus: m };
    match (w, blocks) {
        (64, false) => dp::count::<u64>(n, chk, ring, verbose),
        (64, true) => block::count::<u64>(n, chk, ring, verbose),
        (32, false) => dp::count::<u32>(n, chk, ring, verbose),
        (32, true) => block::count::<u32>(n, chk, ring, verbose),
        (16, false) => dp::count::<u16>(n, chk, ring, verbose),
        (16, true) => block::count::<u16>(n, chk, ring, verbose),
        (8, false) => dp::count::<u8>(n, chk, ring, verbose),
        (8, true) => block::count::<u8>(n, chk, ring, verbose),
        _ => panic!("bad width"),
    }
}

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
        x += prod.checked_mul(t).expect("CRT overflows u128");
        prod = prod.saturating_mul(mm);
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
    /// `u8` residues, number of moduli
    M8(usize),
}

fn count(n: usize, rule: Rule, mode: Mode, blocks: bool, verbose: bool) -> (u128, f64) {
    let chk = Checker::new(n, rule);
    let t = Instant::now();
    let v = match mode {
        Mode::Exact => {
            assert!(n <= 41, "u64 exactness needs N <= 41");
            one(n, &chk, 64, 0, blocks, verbose)
        }
        Mode::M32(q) | Mode::M16(q) | Mode::M8(q) => {
            let w = match mode {
                Mode::M32(_) => 32,
                Mode::M16(_) => 16,
                _ => 8,
            };
            let mods = &moduli(w)[..q];
            let mut res = vec![];
            for &m in mods {
                let r = one(n, &chk, w, m, blocks, verbose) as u64;
                res.push(r);
                if verbose {
                    eprintln!("  N={} residue mod {} = {} ({:.1}s)", n, m, r, t.elapsed().as_secs_f64());
                }
            }
            let x = crt(&res, mods);
            if res.len() >= 2 && verbose {
                // one redundant modulus: if the value is below the product of all but the
                // last modulus, dropping the last residue must give the same answer.
                let y = crt(&res[..res.len() - 1], &mods[..res.len() - 1]);
                eprintln!(
                    "  N={} CRT {} with {} moduli, {} with {} ({})",
                    n,
                    x,
                    res.len(),
                    y,
                    res.len() - 1,
                    if x == y { "stable: verified" } else { "NOT stable: add moduli" }
                );
            }
            x
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
  --mod8 Q    store u8 residues (1/8 the memory), Q runs + CRT, Q<=15
  --blocks    block-streamed layers (free the previous layer block by block, never
              store the middle layer; see block.rs)
  folds residue <rule> N <8|16|32|64> IDX [--blocks]   one residue (IDX into the moduli table)
  folds crt <8|16|32> r0 r1 ...                       CRT of residues for moduli 0, 1, ...
  folds peak N                                         simulated peak memory (words) of --blocks
  --threads   worker threads (default 3)"
    );
    std::process::exit(2)
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut threads = 3usize;
    let mut mode = Mode::Exact;
    let mut verbose = false;
    let mut blocks = false;
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
            "--mod8" => {
                mode = Mode::M8(args[i + 1].parse().unwrap());
                args.drain(i..i + 2);
            }
            "--blocks" => {
                blocks = true;
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
        // split a long CRT computation over several processes
        "residue" => {
            // folds residue <rule> N <8|16|32|64> IDX
            let rule = Rule::parse(&args[1]).unwrap_or_else(|| usage());
            let n: usize = args[2].parse().unwrap();
            let w: usize = args[3].parse().unwrap();
            let q: usize = args[4].parse().unwrap();
            let chk = Checker::new(n, rule);
            let t = Instant::now();
            let m = if w == 64 { 0 } else { moduli(w)[q] };
            let r = one(n, &chk, w, m, blocks, verbose);
            println!(
                "{} N={} mod {} = {} {:.1}s peak_rss {:.2} GB{}",
                rule.name(),
                n,
                m,
                r,
                t.elapsed().as_secs_f64(),
                block::peak_rss() as f64 / 1e9,
                if blocks { " (blocks)" } else { "" }
            );
        }
        "crt" => {
            // folds crt <8|16|32> r0 r1 ...  (residues for moduli 0, 1, ...)
            let w: usize = args[1].parse().unwrap();
            let res: Vec<u64> = args[2..].iter().map(|s| s.parse().unwrap()).collect();
            let mods = &moduli(w)[..res.len()];
            let x = crt(&res, mods);
            let y = crt(&res[..res.len() - 1], &mods[..res.len() - 1]);
            println!("{} ({}) mod 4 = {}", x, if x == y { "stable: verified" } else { "NOT stable: add moduli" }, x % 4);
        }
        "peak" => {
            for a in &args[1..] {
                let n: usize = a.parse().unwrap();
                let w = block::predicted_peak(n);
                println!("N={} peak {} words = {:.2} GB (u8) {:.2} GB (u16) {:.2} GB (u32)", n, w, w as f64 / 1e9, 2.0 * w as f64 / 1e9, 4.0 * w as f64 / 1e9);
            }
        }
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
                let (v, secs) = count(n, rule, mode, blocks, verbose);
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
            if n % 2 == 1 {
                vals.push(("direct", dp::count_direct::<u64>(n, &chk, dp::Ring { modulus: 0 })));
            }
            vals.push(("blocks64", block::count::<u64>(n, &chk, dp::Ring { modulus: 0 }, false)));
            if n <= 18 {
                vals.push(("crt32", count(n, rule, Mode::M32(3), false, false).0));
                vals.push(("crt16", count(n, rule, Mode::M16(6), false, false).0));
                vals.push(("crt16b", count(n, rule, Mode::M16(6), true, false).0));
                vals.push(("crt8b", count(n, rule, Mode::M8(12), true, false).0));
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
