"""Fit growth models to exact a(N) (N <= 33) and SMC estimates (N = 40..512)."""
import math
import numpy as np

pts = {}
for line in open('../semi_counts.txt'):
    if line.startswith('#'):
        continue
    n, v = line.split()[:2]
    pts[int(n)] = math.log(int(v))
smc = {}
for line in open('smc_all.txt'):
    f = dict(t.split('=') for t in line.split() if '=' in t)
    n = int(f['N'])
    smc.setdefault(n, []).append(float(f['loga_est']))
for n, v in smc.items():
    pts[n] = sum(v) / len(v)
Ns = sorted(n for n in pts if n >= 16)
y = np.array([pts[n] for n in Ns])
N = np.array(Ns, float)
L = np.log(N)
lf = np.array([math.lgamma(n + 1) for n in Ns])


def fit(cols, name):
    A = np.column_stack(cols)
    coef, *_ = np.linalg.lstsq(A, y, rcond=None)
    r = y - A @ coef
    print(f"{name}: coef={np.round(coef, 4)}  rms={np.sqrt(np.mean(r**2)):.4f}  max|r|={np.max(np.abs(r)):.4f}")
    return coef


print("points:", Ns)
fit([N * L, N, L, np.ones_like(N)], "c N lnN + b N + d lnN + e")
fit([N * L, N, np.ones_like(N)], "c N lnN + b N + e")
# c = 1 models: y = lnN! - N (alpha lnlnN + beta) + d lnN + e
A = [-N * np.log(L), -N, L, np.ones_like(N)]
A2 = np.column_stack(A)
coef, *_ = np.linalg.lstsq(A2, y - lf, rcond=None)
r = y - lf - A2 @ coef
print(f"lnN! - N(alpha lnlnN + beta) + d lnN + e: coef={np.round(coef, 4)} rms={np.sqrt(np.mean(r**2)):.4f}")
A = [-N * L ** 0.5, -N, L, np.ones_like(N)]
A2 = np.column_stack(A)
coef, *_ = np.linalg.lstsq(A2, y - lf, rcond=None)
r = y - lf - A2 @ coef
print(f"lnN! - N(alpha sqrt(lnN) + beta) + ...: coef={np.round(coef, 4)} rms={np.sqrt(np.mean(r**2)):.4f}")
print("\nlocal two-point exponent c(N1,N2) from y/N = c lnN + b:")
big = [n for n in Ns if n >= 32]
for a_, b_ in zip(big, big[1:]):
    c = (pts[b_] / b_ - pts[a_] / a_) / (math.log(b_) - math.log(a_))
    print(f"  {a_:4d}-{b_:4d}: c = {c:.3f}")
print("\ndeficit d(N) = (lnN! - ln a)/N and d/lnN:")
for n in big:
    d = (math.lgamma(n + 1) - pts[n]) / n
    print(f"  N={n:4d} d={d:.4f} d/lnN={d / math.log(n):.4f} exp(d)/lnN={math.exp(d) / math.log(n):.4f}")
