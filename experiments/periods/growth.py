"""growth.py RUNFILE [RUNFILE ...]: decay of the continuum acceptance p_k = c_k / c_{k-1}.

Exact c_1..c_8 (vol.py) and SMC estimates (cont.c) for k up to 4096.  The SMC p_k are averaged
over the run files and over windows of k (they are noisy per step).  Fits on k in [kmin, kmax]:
   log model:    1/p = (ln k + b) / A          (p ~ A / ln k)
   power model:  ln p = ln C - alpha ln k      (p ~ C k^-alpha)
   mixed:        ln p = ln C - alpha ln k - beta ln ln k
and the local exponents  -d ln p / d ln k  and  d (1/p) / d ln k  in octaves of k.
Also the continuum imbalance  s_k^2 = int_0^1 F(c)^2 dc  and the local-CLT constant
G_k = sqrt(2 pi) s_k p_k (cf. ../asymptotics/NOTES.txt, where G ~ 1.02-1.05 in the discrete case).
"""
import sys
from fractions import Fraction as F
import numpy as np

exact = [F(1), F(1, 2), F(2, 9), F(4283, 48384), F(6214319, 203212800),
         F(21205971559, 2031997943808), F(12908310624317597, 3982715969863680000),
         F(5766402363187232751941221, 5807018243102153166028800000)]

runs = []
for fn in sys.argv[1:]:
    d = {}
    for l in open(fn):
        if l.startswith('#'):
            continue
        p = l.split()
        if len(p) >= 5:
            d[int(p[0])] = (float(p[1]), float(p[4]))
    runs.append(d)
K = min(max(d) for d in runs)
ks = np.arange(2, K + 1)
p = np.array([np.mean([d[k][0] for d in runs]) for k in ks])
s2 = np.array([np.mean([d[k][1] for d in runs]) for k in ks])
# the integral of F^2 is recorded BEFORE the k-th point is added, i.e. for k-1 points
print('exact vs SMC p_k:')
for k in range(2, 9):
    pe = float(exact[k - 1] / exact[k - 2])
    print(f'  k={k}: exact {pe:.6f}  smc {p[k - 2]:.6f}   k!c_k = {float(exact[k - 1]) * np.prod(range(1, k + 1)):.4f}')

print('\noctave averages (geometric windows [2^j, 2^(j+1))):')
print('   k-range        <p>       <1/p>   <s^2>    G=sqrt(2pi)s p')
j = 3
while 2 ** (j + 1) <= K + 1:
    m = (ks >= 2 ** j) & (ks < 2 ** (j + 1))
    pm = p[m].mean()
    sm = s2[m].mean()
    print(f'  [{2**j:5d},{2**(j+1):5d})  {pm:.5f}  {np.mean(1/p[m]):8.3f}  {sm:7.3f}  {np.sqrt(2*np.pi*sm)*pm:.4f}')
    j += 1


def fit(kmin, kmax):
    m = (ks >= kmin) & (ks <= kmax)
    x, y = np.log(ks[m]), p[m]
    # log model: 1/p linear in ln k
    A1 = np.vstack([x, np.ones_like(x)]).T
    c1, *_ = np.linalg.lstsq(A1, 1 / y, rcond=None)
    r1 = np.sqrt(np.mean((np.log(1 / (A1 @ c1)) - np.log(y)) ** 2))
    # power model
    c2, *_ = np.linalg.lstsq(A1, np.log(y), rcond=None)
    r2 = np.sqrt(np.mean((A1 @ c2 - np.log(y)) ** 2))
    # mixed
    A3 = np.vstack([x, np.log(x), np.ones_like(x)]).T
    c3, *_ = np.linalg.lstsq(A3, np.log(y), rcond=None)
    r3 = np.sqrt(np.mean((A3 @ c3 - np.log(y)) ** 2))
    return c1, r1, c2, r2, c3, r3


print('\nfits (rms residual in ln p):')
for kmin, kmax in [(16, K), (64, K), (256, K), (16, 512), (512, K)]:
    c1, r1, c2, r2, c3, r3 = fit(kmin, kmax)
    print(f'  k in [{kmin},{kmax}]:  p = {1/c1[0]:.4f}/(ln k + {c1[1]/c1[0]:.3f})  rms {r1:.4f}  | '
          f'p = {np.exp(c2[1]):.4f} k^-{-c2[0]:.4f}  rms {r2:.4f}  | '
          f'mixed alpha={-c3[0]:.4f} beta={-c3[1]:.3f} rms {r3:.4f}')

print('\nout-of-sample: fit on [16, 512], predict octave means above 512:')
c1, r1, c2, r2, c3, r3 = fit(16, 512)
j = 9
while 2 ** (j + 1) <= K + 1:
    m = (ks >= 2 ** j) & (ks < 2 ** (j + 1))
    x = np.log(ks[m])
    print(f'  [{2**j},{2**(j+1)}): measured {p[m].mean():.5f}   log-model {np.mean(1/(c1[0]*x+c1[1])):.5f}'
          f'   power-model {np.mean(np.exp(c2[0]*x+c2[1])):.5f}')
    j += 1
