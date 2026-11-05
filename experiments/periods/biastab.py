"""biastab.py: octave means of the continuum SMC (p_k and s^2 = int F^2 in parentheses) for
several population sizes M; the 1/M extrapolation p(inf) ~ p(M) + (p(M) - p(M/2 or M/4)).(...)
from the two largest M available for that octave; and fits of the extrapolated octave means:
   log model    1/p = alpha ln k + beta           (p ~ 1/(alpha (ln k + b)))
   power model  ln p = ln C - gamma ln k
plus local exponents per octave.  Octave mean of p over [lo, 2lo) is attributed to the
geometric centre k = lo sqrt 2."""
import numpy as np


def load(f):
    d = {}
    for l in open(f):
        p = l.split()
        if len(p) >= 5:
            d[int(p[0])] = (float(p[1]), float(p[4]))
    return d


R = {1000: load('runs/cont_1024_1000_s41.txt'), 4000: load('runs/cont_K2600_M4000_s11.txt'),
     16000: load('runs/cont_1024_16000_s21.txt'), 32000: load('runs/cont_1024_32000_s51.txt'),
     64000: load('runs/cont_512_64000_s31.txt')}
oct_k, oct_p, oct_s = [], [], []
for lo in [8, 16, 32, 64, 128, 256, 512]:
    ks = range(lo, min(2 * lo, 1024))
    row = [(M, np.mean([d[k][0] for k in ks]), np.mean([d[k][1] for k in ks]))
           for M, d in sorted(R.items()) if max(d) >= max(ks)]
    (M1, p1, s1), (M2, p2, s2) = row[-2], row[-1]
    r = M2 / M1
    ext = p2 + (p2 - p1) / (r - 1)          # bias ~ 1/M
    exts = s2 + (s2 - s1) / (r - 1)
    print(f'[{lo},{2*lo})', ' '.join(f'M={M}: {p:.5f} ({s:.2f})' for M, p, s in row),
          f'  extrap p {ext:.5f}  s^2 {exts:.2f}')
    oct_k.append(lo * np.sqrt(2))
    oct_p.append(ext)
    oct_s.append(exts)
k, p, s2 = np.array(oct_k), np.array(oct_p), np.array(oct_s)
print('\noctave  1/p   d(1/p)  local exponent -dlnp/dlnk   s=sqrt(s^2)  ds   G=sqrt(2pi)s p')
for i in range(len(k)):
    d1 = (1 / p[i] - 1 / p[i - 1]) if i else float('nan')
    le = -np.log(p[i] / p[i - 1]) / np.log(2) if i else float('nan')
    ds = np.sqrt(s2[i]) - np.sqrt(s2[i - 1]) if i else float('nan')
    print(f'{k[i]:8.1f} {1/p[i]:6.3f} {d1:6.3f}   {le:6.3f}               {np.sqrt(s2[i]):6.3f} {ds:6.3f}  {np.sqrt(2*np.pi*s2[i])*p[i]:.3f}')
x = np.log(k)
for lo in [0, 2]:
    X = np.vstack([x[lo:], np.ones_like(x[lo:])]).T
    a, *_ = np.linalg.lstsq(X, 1 / p[lo:], rcond=None)
    r1 = np.sqrt(np.mean((np.log(1 / (X @ a)) - np.log(p[lo:])) ** 2))
    g, *_ = np.linalg.lstsq(X, np.log(p[lo:]), rcond=None)
    r2 = np.sqrt(np.mean((X @ g - np.log(p[lo:])) ** 2))
    print(f'octaves from k={k[lo]:.0f}: log model p = 1/({a[0]:.4f} ln k + {a[1]:.4f})'
          f' = {1/a[0]:.4f}/(ln k + {a[1]/a[0]:.3f}), rms {r1:.4f};'
          f'  power p = {np.exp(g[1]):.4f} k^-{-g[0]:.4f}, rms {r2:.4f}')
    Xs = np.vstack([x[lo:], np.ones_like(x[lo:])]).T
    b, *_ = np.linalg.lstsq(Xs, np.sqrt(s2[lo:]), rcond=None)
    print(f'      s = {b[0]:.4f} ln k + {b[1]:.4f}')
