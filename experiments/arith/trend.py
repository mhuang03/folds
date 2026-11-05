"""Residuals of log a(N) against a smooth trend, by N mod q.
Model per parity class: log a = A + B N + C N log N + D log N  (+ indicator terms).
Uses N = 8..33. Also the same for log c(N) (self-dual counts, N = 2n only)."""
import numpy as np
from math import log, lgamma
from data import a, load_selfdual


def fit(Ns, y, extra=None):
    X = [[1, N, N * log(N), log(N)] + ([f(N) for f in extra] if extra else []) for N in Ns]
    X = np.array(X, float); y = np.array(y, float)
    coef, res, *_ = np.linalg.lstsq(X, y, rcond=None)
    r = y - X @ coef
    dof = len(y) - X.shape[1]
    s2 = (r @ r) / max(dof, 1)
    cov = s2 * np.linalg.inv(X.T @ X)
    return coef, r, np.sqrt(np.diag(cov))


for par in (0, 1):
    Ns = [N for N in range(8, 34) if N % 2 == par]
    y = [log(a[N]) for N in Ns]
    coef, r, se = fit(Ns, y)
    print(f"parity {par}: residuals (no mod-3 term)")
    print("   ", " ".join(f"{N}:{x:+.3f}" for N, x in zip(Ns, r)))
    for q in (3, 4, 5):
        for res_ in range(q):
            vals = [x for N, x in zip(Ns, r) if N % q == res_]
            if vals:
                print(f"    N≡{res_} mod {q}: mean {np.mean(vals):+.4f} (n={len(vals)})")
    coef, r, se = fit(Ns, y, [lambda N: 1.0 if N % 3 == 0 else 0.0])
    print(f"   with [3|N] indicator: coef {coef[-1]:+.4f} ± {se[-1]:.4f}; resid sd {np.std(r):.4f}")
    coef, r, se = fit(Ns, y, [lambda N: 1.0 if N % 4 in (0, 1) else 0.0])
    print(f"   with [N≡0,1 mod 4] indicator: coef {coef[-1]:+.4f} ± {se[-1]:.4f}")
    coef, r, se = fit(Ns, y, [lambda N: 1.0 if N % 5 == 0 else 0.0])
    print(f"   with [5|N] indicator: coef {coef[-1]:+.4f} ± {se[-1]:.4f}")

c = load_selfdual()
for cls, name in ((lambda N: N % 2 == 0, "c(2n)"), (lambda N: N % 4 == 1, "c(4n+1)")):
    Ns = [N for N in sorted(c) if cls(N) and N >= 8 and c[N] > 0]
    y = [log(c[N]) for N in Ns]
    coef, r, se = fit(Ns, y)
    print(name, "residuals:", " ".join(f"{N}:{x:+.3f}" for N, x in zip(Ns, r)))
    for q in (3, 4, 8):
        print("   by N mod", q, {res_: round(float(np.mean([x for N, x in zip(Ns, r) if N % q == res_])), 3)
                                 for res_ in range(q) if any(N % q == res_ for N in Ns)})
