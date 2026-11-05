"""Asymptotic fits for log a(N)."""
import math
import numpy as np
from common import A

N = np.arange(1, len(A) + 1)
la = np.array([math.log(a) for a in A])
lf = np.array([math.lgamma(n + 1) for n in N])
print("N  log a/log N!   (log a - 0.5 log N!)/N   ratio a(N)/a(N-1)/N^0.5")
for i, n in enumerate(N):
    r = A[i] / A[i - 1] / math.sqrt(n) if i else float('nan')
    print(n, round(la[i] / lf[i], 4) if n > 1 else '-', round((la[i] - 0.5 * lf[i]) / n, 4), round(r, 4))

def fit(mask, cols, names):
    X = np.stack([c[mask] for c in cols], 1)
    coef, *_ = np.linalg.lstsq(X, la[mask], rcond=None)
    res = la[mask] - X @ coef
    print("  ", ", ".join(f"{nm}={c:.4f}" for nm, c in zip(names, coef)), " max|res|=%.3g" % abs(res).max())

lnN = np.log(N)
for par, nm in [(0, "even"), (1, "odd"), (None, "all")]:
    m = (N >= 9) & ((N % 2 == par) if par is not None else True)
    print(nm)
    fit(m, [N * lnN, N, lnN, np.ones_like(lnN)], ["alpha(NlogN)", "beta(N)", "gamma(logN)", "delta"])
    fit(m, [0.5 * lf, N, lnN, np.ones_like(lnN)], ["c(logN!)", "beta(N)", "gamma(logN)", "delta"])
    # fixed alpha = 1/2 test
    y = la - 0.5 * lf
    X = np.stack([N, lnN, np.ones_like(lnN)], 1)[m]
    coef, *_ = np.linalg.lstsq(X, y[m], rcond=None)
    print("   alpha fixed 1/2 (in log N!): beta=%.4f gamma=%.4f delta=%.4f maxres=%.3g" % (*coef, abs(y[m] - X @ coef).max()))
