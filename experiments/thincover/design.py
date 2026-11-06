"""design.py: for a 2-parameter line piece (v = u + off or v = 2u + off) and a slice option, find a
linear c0 = (a + b u + g N)/q inside all exact windows (side (1, 0)) on a sample, check the active
lower bounds at c0 and c0 + 1, and report.
usage: python3 design.py cls off parity o f t p j umin"""
import sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from slicelib import cons, window, maxlow


def pts(cls, off, par, umin, Ns):
    for N in Ns:
        if N % 2 != par:
            continue
        for u in range(umin, N):
            v = u + off if cls == 1 else 2 * u + off
            if u + 2 * v + 1 > N:
                break
            if (u + v - N) % 2:
                continue
            if cls == 2 and (N > 8 * u + 320 or v < u + 10):
                continue
            if cls == 1 and off == 1 and 3 * u + 21 <= N:
                continue
            yield N, u, v


def sampleN(par):
    Ns = list(range(301, 420)) + list(range(420, 1200, 7)) + list(range(1200, 4000, 41)) + [10001, 10002, 30001, 30002]
    return [N for N in Ns if N % 2 == par]


def fitlin(data, q=None):
    X = np.array([[1, u, N] for N, u, lo, hi in data], float)
    lo = np.array([float(x[2]) for x in data]); hi = np.array([float(x[3]) for x in data])
    A = np.vstack([np.hstack([-X, np.ones((len(X), 1))]), np.hstack([X, np.ones((len(X), 1))])])
    b = np.concatenate([-lo, hi])
    r = linprog([0, 0, 0, -1], A_ub=A, b_ub=b, bounds=[(None, None)] * 4, method='highs')
    return (r.x[:3], r.x[3]) if r.status == 0 else (None, None)


def rationalise(c, data, dens=(1, 2, 3, 4, 6, 8, 12, 16, 24, 30, 36, 48, 60, 120, 240, 1000, 10000)):
    """round coefficients (a, b, g) to fractions with a common small denominator; check windows."""
    for q in dens:
        cand = [F(round(x * q), q) for x in c]
        ok = all(lo <= cand[0] + cand[1] * u + cand[2] * N <= hi for N, u, lo, hi in data)
        if ok:
            return cand
    return None


def actwin(cs, w, i0, i1):
    """restrict the window so that lower bound i0 is the max at c0 and i1 at c0 + 1."""
    lo, hi = w
    A0, C0, D0 = cs[i0]
    A1, C1, D1 = cs[i1]
    for k, (A, C, D) in enumerate(cs):
        if A <= 0:
            continue
        for (Ai, Ci, Di, sh) in ((A0, C0, D0, 0), (A1, C1, D1, 1)):
            # -(Ci c + Di)/Ai >= -(C c + D)/A  at c = c0 + sh
            # (C/A - Ci/Ai) c >= Di/Ai - D/A
            e = F(C, A) - F(Ci, Ai)
            r = F(Di, Ai) - F(D, A) - e * sh
            if e == 0:
                if r > 0:
                    return None
            elif e > 0:
                lo = max(lo, r / e)
            else:
                hi = min(hi, r / e)
    return (lo, hi) if lo <= hi else None


def design(cls, off, par, opt, umin, Ns=None, verbose=True, act=None):
    Ns = Ns or sampleN(par)
    best = None
    combos = [act] if act else [(1, 1), (1, 3), (3, 1), (3, 3)]
    for i0, i1 in combos:
        r = design1(cls, off, par, opt, umin, Ns, i0, i1)
        if verbose:
            print((i0, i1), r)
        if r and r[0] != 'bad' and (best is None or r[1] > best[1]):
            best = r + ((i0, i1),)
    return best


def design1(cls, off, par, opt, umin, Ns, i0, i1):
    data, bad = [], []
    for N, u, v in pts(cls, off, par, umin, Ns):
        cs = cons(N, u, v, opt, exact_smax=False)
        w = window(cs)
        if w is not None and w[0] <= w[1]:
            w = actwin(cs, w, i0, i1)
        if w is None or w[0] > w[1]:
            bad.append((N, u))
        else:
            data.append((N, u, w[0], w[1]))
    if bad:
        return ('bad', bad[:6], len(bad))
    c, t = fitlin(data)
    if c is None:
        return None
    cr = rationalise(c, data)
    if cr is None:
        return None
    return cr, t


if __name__ == '__main__':
    a = list(map(int, sys.argv[1:]))
    cls, off, par, o, f, t, p, j, umin = a
    print(design(cls, off, par, (o, f, t, p, j), umin))
