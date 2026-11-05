"""Print the table of section 3.2 of NOTES.txt from the run files."""
import glob, math, re
from collections import defaultdict
import numpy as np

est = defaultdict(lambda: defaultdict(list))
for fn in ['runs/prod.txt', 'runs/pscan.txt', 'runs/big.txt']:
    for l in open(fn):
        m = re.match(r'N=(\d+) P=(\d+) Pmax=\d+ loga_est=([\d.]+)', l)
        if m:
            est[int(m[1])][int(m[2])].append(float(m[3]))
diag = defaultdict(dict)
for fn in glob.glob('runs/d_*_*_*.txt'):
    N, P, s = map(int, re.findall(r'd_(\d+)_(\d+)_(\d+)', fn)[0])
    rows = [dict((t.split('=')[0], t.split('=')[1]) for t in l.split()) for l in open(fn)]
    if not rows or float(rows[-1]['t']) < 0.98:
        continue
    half = [r for r in rows if abs(float(r['t']) - 0.5) < 0.5 / 64][0]
    lt = [math.log(float(r['sdJ'])) for r in rows if 0 < float(r['t']) < 0.99 and float(r['sdJ']) > 0]
    g = [math.log(math.sqrt(2 * math.pi) * float(r['sdJ']) * float(r['frac'])) for r in rows
         if 0 < float(r['t']) < 0.99 and float(r['sdJ']) > 0]
    diag[N].setdefault(P, []).append((float(half['sdJ']), math.exp(np.mean(lt)), np.mean(g)))
print("      N    ln a(N)     sd     d(N)  e^d/lnN  sigma(1/2) sigma_bar   G_bar")
for N in sorted(est):
    Pm = max(est[N]); v = est[N][Pm]; mu = np.mean(v)
    sd = np.std(v, ddof=1) if len(v) > 1 else float('nan')
    d = (math.lgamma(N + 1) - mu) / N
    dg = diag[N].get(max(diag[N])) if diag[N] else None
    s12, sb, g = (np.mean([x[i] for x in dg]) for i in range(3)) if dg else (float('nan'),) * 3
    print(f"  {N:5d} {mu:10.1f} {sd:6.1f} {d:8.4f} {math.exp(d) / math.log(N):8.4f} {s12:9.3f} "
          f"{sb:9.3f} {math.exp(g):8.3f}   (P={Pm}, {len(v)} runs)")
