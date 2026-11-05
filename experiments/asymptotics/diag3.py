"""Summarise smc3 diagnostics (runs/d_N_P_seed.txt), averaged over the available runs with
the largest P for each N: acceptance frac = V/(N-k), sdJ, Dmax, structure function SE(l)
of the discrepancy, at t = k/N in {1/8, 1/4, 1/2, 3/4}; and integrated quantities
   A(N) = mean_k log(frac_k)          (so log a(N) ~ log N! + N A(N))
   G(N) = mean_k log(sqrt(2 pi) sdJ_k frac_k)  (local CLT check: 0 if frac = 1/(sqrt(2pi) sdJ))."""
import glob, math, re, sys
from collections import defaultdict

runs = defaultdict(list)
for fn in glob.glob('runs/d_*_*_*.txt'):
    N, P, s = map(int, re.findall(r'd_(\d+)_(\d+)_(\d+)', fn)[0])
    rows = []
    for line in open(fn):
        d = {}
        for tok in line.split():
            k, v = tok.split('=')
            d[k] = [float(x) for x in v.split(',')] if k == 'SE' else float(v)
        rows.append(d)
    if rows and rows[-1]['t'] > 0.98:
        runs[N].append((P, rows))

def avg(rowsets, key, t):
    vals = []
    for rows in rowsets:
        for r in rows:
            if abs(r['t'] - t) < 0.5 / 64:
                vals.append(r[key])
    return sum(vals) / len(vals) if vals else float('nan')

out = []
print("  N  runs  t     frac    sdJ    Dmax   frac*sdJ*sqrt(2pi)")
for N in sorted(runs):
    Pm = max(p for p, _ in runs[N])
    rs = [r for p, r in runs[N] if p == Pm]
    for t in (0.125, 0.25, 0.5, 0.75):
        f, s, d = avg(rs, 'frac', t), avg(rs, 'sdJ', t), avg(rs, 'Dmax', t)
        print(f"{N:5d} {len(rs):3d} {t:.3f} {f:.4f} {s:6.3f} {d:6.3f}   {f * s * math.sqrt(2 * math.pi):.3f}")
    # integrated (checkpoints only, t in (0,1))
    A = []; G = []
    for rows in rs:
        A.append(sum(math.log(r['frac']) for r in rows if r['t'] < 0.99) / len([r for r in rows if r["t"] < 0.99 and r["sdJ"] > 0]))
        G.append(sum(math.log(math.sqrt(2 * math.pi) * r['sdJ'] * r['frac']) for r in rows if r["t"] < 0.99 and r["sdJ"] > 0)
                 / len([r for r in rows if r["t"] < 0.99 and r["sdJ"] > 0]))
    out.append((N, sum(A) / len(A), sum(G) / len(G)))
print("\n  N   mean_t log frac   mean_t log(sqrt(2pi) sdJ frac)")
for N, a, g in out:
    print(f"{N:5d}   {a:8.4f}   {g:8.4f}")
if '-se' in sys.argv:
    print("\nstructure function SE(l), l = 1,2,4,... at t = 1/2")
    for N in sorted(runs):
        Pm = max(p for p, _ in runs[N]); rs = [r for p, r in runs[N] if p == Pm]
        se = None; n = 0
        for rows in rs:
            for r in rows:
                if abs(r['t'] - 0.5) < 0.5 / 64:
                    se = r['SE'] if se is None else [a + b for a, b in zip(se, r['SE'])]; n += 1
        print(f"{N:5d} " + " ".join(f"{x / n:.2f}" for x in se))
