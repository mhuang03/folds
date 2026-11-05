"""Summarise the smc2 diagnostics (runs/st_N.txt): acceptance fraction p0 = V/(N-k),
sd of the imbalance field J over free panels, max discrepancy, and the J histogram."""
import math, sys, os

def load(N):
    rows = []
    fn = f'runs/st_{N}.txt'
    if not os.path.exists(fn):
        return rows
    for line in open(fn):
        d = {}
        for tok in line.split():
            k, v = tok.split('=')
            d[k] = [float(x) for x in v.split(',')] if k == 'hist' else float(v)
        rows.append(d)
    return rows

Ns = [int(a) for a in sys.argv[1:]] or [64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384]
print(" N      t    frac   Dmax    sdJ   madJ  frac*sdJ*sqrt(2pi)  frac*Dmax  h(0)/h(1)  h(0)/h(2) kurt")
for N in Ns:
    for r in load(N):
        if abs(r['t'] - 0.5) < 1e-3 or abs(r['t'] - 0.25) < 1e-3:
            h = r['hist']; c = 40
            m2 = sum(h[c + i] * i * i for i in range(-40, 41)); m4 = sum(h[c + i] * i ** 4 for i in range(-40, 41))
            hs = sum(h)
            print(f"{N:5d} {r['t']:.3f} {r['frac']:.4f} {r['Dmax']:6.3f} {r['sdJ']:6.3f} {r['madJ']:6.3f}"
                  f"   {r['frac'] * r['sdJ'] * math.sqrt(2 * math.pi):.3f}            {r['frac'] * r['Dmax']:.3f}"
                  f"     {h[c] / (0.5 * (h[c - 1] + h[c + 1])):.3f}     {h[c] / (0.5 * (h[c - 2] + h[c + 2])):.3f}"
                  f"  {m4 / hs / (m2 / hs) ** 2:.2f}")
