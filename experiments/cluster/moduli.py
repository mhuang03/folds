"""Arithmetic effects in y(N) = log(a/aW): regress y on a smooth per-parity background plus
indicators [d | N] (and [N = d k - 1], [N = d k + 1] for d = 3), report coefficients and t-like
ratios.  Also the residue-class averages of the bump b(N) = y(N) - (y(N-2)+y(N+2))/2."""
import math
import numpy as np
from wallis_exact import log_aW, A

Ns = np.arange(1, len(A) + 1)
y = np.array([math.log(A[N - 1]) - log_aW(N) for N in Ns])


def fit(Nmin, ds, deg=3, extra=()):
    sel = Ns >= Nmin
    N = Ns[sel].astype(float)
    cols, names = [], []
    for p in (0, 1):
        par = (Ns[sel] % 2 == p).astype(float)
        for k in range(deg + 1):
            cols.append(par * (N / 30.0) ** k)
            names.append("par%d*N^%d" % (p, k))
    for d in ds:
        cols.append((Ns[sel] % d == 0).astype(float))
        names.append("[%d|N]" % d)
    for nm, f in extra:
        cols.append(np.array([f(n) for n in Ns[sel]], float))
        names.append(nm)
    X = np.array(cols).T
    beta, res, rk, sv = np.linalg.lstsq(X, y[sel], rcond=None)
    r = y[sel] - X @ beta
    dof = len(N) - X.shape[1]
    s2 = (r @ r) / dof
    cov = s2 * np.linalg.inv(X.T @ X)
    return names, beta, np.sqrt(np.diag(cov)), math.sqrt(s2), r


if __name__ == "__main__":
    for ds in ([], [3], [3, 4], [3, 5], [3, 7], [3, 4, 5, 7], [3, 6, 9]):
        names, b, se, s, r = fit(10, ds)
        out = ", ".join("%s=%.4f(%.4f)" % (n, bb, e) for n, bb, e in zip(names, b, se) if n.startswith("["))
        print("ds=%-12s rms=%.4f  %s" % (ds, s, out))
    for Nmin in (8, 10, 14, 18):
        for deg in (2, 3, 4):
            names, b, se, s, r = fit(Nmin, [3], deg=deg, extra=(("[N%3==2]", lambda n: n % 3 == 2),))
            print("Nmin=%d deg=%d rms=%.4f  " % (Nmin, deg, s) + ", ".join("%s=%.4f(%.4f)" % (n, bb, e) for n, bb, e in zip(names, b, se) if n.startswith("[")))
    names, b, se, s, r = fit(10, [3], extra=(("[3|N]*(30/N)", lambda n: (n % 3 == 0) * 30.0 / n),))
    print("decay test: " + ", ".join("%s=%.4f(%.4f)" % (n, bb, e) for n, bb, e in zip(names, b, se) if n.startswith("[")))
    for nm, f in (("[3|N]*sqrt(30/N)", lambda n: (n % 3 == 0) * (30.0 / n) ** 0.5), ("[3|N]*(30/N)", lambda n: (n % 3 == 0) * 30.0 / n)):
        names, b, se, s, r = fit(10, [], extra=((nm, f),))
        print("single-form fit %s: coef=%.4f(%.4f) rms=%.4f" % (nm, b[-1], se[-1], s))
    names, b, se, s, r = fit(10, [3])
    print("constant form: rms=%.4f" % s)
    print("constant-form fit: " +", ".join("%s=%.4f(%.4f)" % (n, bb, e) for n, bb, e in zip(names, b, se) if n.startswith("[")))
    names, b, se, s, r = fit(10, [3])
    print("residuals after [3|N] fit (N>=10):", " ".join("%d:%+.3f" % (n, v) for n, v in zip(Ns[Ns >= 10], r)))
    print()
    print("bump averages by residue class (N=8..31), after subtracting the mean bump of the class N%3!=0:")
    bump = {N: y[N - 1] - (y[N - 3] + y[N + 1]) / 2 for N in range(8, 32)}
    for d in (3, 4, 5, 6, 7, 8, 9):
        for N0 in (8, 14):
            vals = {}
            for N, v in bump.items():
                if N >= N0:
                    vals.setdefault(N % d, []).append(v)
            print("d=%d N>=%d " % (d, N0) + " ".join("%d:%+.4f(n=%d)" % (k, np.mean(v), len(v)) for k, v in sorted(vals.items())))
