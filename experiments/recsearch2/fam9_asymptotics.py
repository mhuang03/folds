"""Family 9 (literature priority 4): asymptotic model selection, per parity.

y(N) = ln a(N) - ln N!   fitted on N = N0..38 separately for even and odd N (and mod 3
classes).  Models (all with free alpha ln N + beta):
  MA  -N ln(kappa ln N)                       (README conjecture)           params: kappa
  MB  -c N lnln N + b N                                                     params: c, b
  MC  Bell saddle for F = exp(lam (e^{cz}-1)/c):  a(N)/N! ~ [z^N]F, r solves lam r e^{c r} = N,
      y = lam (e^{cr}-1)/c - N ln r - 1/2 ln(2 pi N (1 + c r))              params: lam, c
  MD  -N ln(kappa ln N) + g N/ln N (one more correction term)               params: kappa, g
Reported: RMS residual, max residual, and the leave-last-3-out prediction error (fit on
N0..N_max-6 of that parity, predict the last 3 of that parity).  Floats (mpmath for the
log of huge integers); this is model selection, not an exact test."""
import numpy as np
from math import lgamma, log, pi
from scipy.optimize import least_squares
from scipy.special import lambertw
from common2 import A, NMAX

lnA = {N: (len(str(A[N])) and float(__import__('mpmath').log(A[N]))) for N in range(1, NMAX + 1)}
y = {N: lnA[N] - lgamma(N + 1) for N in lnA}


def design(model, N, p):
    N = np.asarray(N, float)
    L = np.log(N)
    LL = np.log(L)
    if model == 'MA':
        (k,) = p
        f = -N * (np.log(k) + LL)
    elif model == 'MB':
        c, b = p
        f = -c * N * LL + b * N
    elif model == 'MD':
        k, g = p
        f = -N * (np.log(k) + LL) + g * N / L
    elif model == 'MC':
        lam, c = p
        r = np.real(lambertw(c * N / lam)) / c
        f = lam * (np.exp(c * r) - 1) / c - N * np.log(r) - 0.5 * np.log(2 * pi * N * (1 + c * r))
    return f


P0 = {'MA': [0.5], 'MB': [1.0, 0.0], 'MD': [0.5, 0.0], 'MC': [1.0, 1.0]}
BOUNDS = {'MA': ([1e-3], [50]), 'MB': ([-10, -10], [10, 10]), 'MD': ([1e-3, -50], [50, 50]),
          'MC': ([1e-3, 1e-3], [1e3, 50])}


def fit(model, Ns):
    Ns = np.asarray(Ns, float)
    Y = np.array([y[int(n)] for n in Ns])

    def resid(p):
        f = design(model, Ns, p)
        X = np.vstack([np.log(Ns), np.ones_like(Ns)]).T
        coef, *_ = np.linalg.lstsq(X, Y - f, rcond=None)
        return Y - f - X @ coef

    best = None
    for s in ([1], [0.3], [3]) if True else []:
        p0 = [v * s[0] for v in P0[model]] if model != 'MB' else P0[model]
        p0 = np.clip(p0, np.array(BOUNDS[model][0]) + 1e-6, np.array(BOUNDS[model][1]) - 1e-6)
        r = least_squares(resid, p0, bounds=BOUNDS[model])
        if best is None or r.cost < best.cost:
            best = r
    p = best.x
    f = design(model, Ns, p)
    X = np.vstack([np.log(Ns), np.ones_like(Ns)]).T
    coef, *_ = np.linalg.lstsq(X, Y - f, rcond=None)
    return p, coef


def predict(model, p, coef, Ns):
    Ns = np.asarray(Ns, float)
    return design(model, Ns, p) + coef[0] * np.log(Ns) + coef[1]


N0 = 12
classes = {'even N': [N for N in range(N0, NMAX + 1) if N % 2 == 0],
           'odd N': [N for N in range(N0, NMAX + 1) if N % 2 == 1],
           'N=0 mod 3': [N for N in range(N0, NMAX + 1) if N % 3 == 0],
           'N=+-1 mod 6': [N for N in range(N0, NMAX + 1) if N % 6 in (1, 5)],
           'all N': list(range(N0, NMAX + 1))}
print(f"fits of y = ln a(N) - ln N!, N >= {N0}; extra free terms alpha ln N + beta in every model")
print(f"{'class':12s} {'model':4s} {'#par':>4s} {'params':>28s} {'rms':>9s} {'maxres':>9s} {'pred.err(last3)':>16s}")
for cname, Ns in classes.items():
    for m in ('MA', 'MB', 'MC', 'MD'):
        p, coef = fit(m, Ns)
        res = np.array([y[n] for n in Ns]) - predict(m, p, coef, Ns)
        p2, c2 = fit(m, Ns[:-3])
        pe = np.array([y[n] for n in Ns[-3:]]) - predict(m, p2, c2, Ns[-3:])
        npar = len(p) + 2
        ps = ' '.join(f'{v:.4g}' for v in list(p) + list(coef))
        print(f"{cname:12s} {m:4s} {npar:4d} {ps:>28s} {np.sqrt(np.mean(res**2)):9.2e} {np.max(abs(res)):9.2e} {np.max(abs(pe)):16.2e}")
    print()
