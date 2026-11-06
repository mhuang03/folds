"""fastfit.py: float version of the nu0 design for cluster pieces (exploration): windows in floats,
LP fit of nu0 in given features, slack, and the binding points.
python3 fastfit.py NAME [quad] [Ns]"""
import sys
import numpy as np
import sympy as sp
from scipy.optimize import linprog
from clpieces import cl_piece, N, u, v, r, dl
from design2 import points, tforms


def windows_float(cs):
    cs = [(float(A), float(C), float(D)) for A, C, D in cs]
    lo, hi = -1e18, 1e18
    for A, C, D in cs:
        if A == 0:
            if C > 0:
                lo = max(lo, -D / C)
            elif C < 0:
                hi = min(hi, -D / C)
            elif D < 0:
                return None
    for Al, Cl, Dl in cs:
        if Al <= 0:
            continue
        for Au, Cu, Du in cs:
            if Au >= 0:
                continue
            e = Al * Cu + (-Au) * Cl
            f_ = Al * (-Au) - Al * Du - (-Au) * Dl
            if e > 0:
                lo = max(lo, f_ / e)
            elif e < 0:
                hi = min(hi, f_ / e)
            elif f_ > 0:
                return None
    return lo, hi - 1


def maxlow_f(cs, c):
    best, arg = None, None
    for i, (A, C, D) in enumerate(cs):
        A, C, D = float(A), float(C), float(D)
        if A > 0:
            val = -(C * c + D) / A
            if best is None or val > best:
                best, arg = val, i
    return arg


def actwin_f(cs, w, i0, i1):
    lo, hi = w
    f = [(float(A), float(C), float(D)) for A, C, D in cs]
    A0, C0, D0 = f[i0]
    A1, C1, D1 = f[i1]
    for A, C, D in f:
        if A <= 0:
            continue
        for (Ai, Ci, Di, sh) in ((A0, C0, D0, 0), (A1, C1, D1, 1)):
            e = C / A - Ci / Ai
            rr = Di / Ai - D / A - e * sh
            if abs(e) < 1e-15:
                if rr > 1e-12:
                    return None
            elif e > 0:
                lo = max(lo, rr / e)
            else:
                hi = min(hi, rr / e)
    return (lo, hi) if lo <= hi else None


def run(nm, quad=False, Ns=None):
    pc = cl_piece(nm)
    Ns = Ns or list(range(301, 1001, 7)) + [1000, 1500, 3000, 10000, 30000]
    pts = points(pc, Ns)
    data = []
    for pt, (Nn, uu, vv) in pts:
        cs = tforms(pc.opt, Nn, uu, vv, pc.dirn, 'pf')
        w = windows_float(cs)
        data.append((pt, cs, w))
    from collections import Counter
    cnt = Counter()
    for pt, cs, w in data:
        if w and w[0] <= w[1]:
            c = (w[0] + w[1]) / 2
            cnt[(maxlow_f(cs, c), maxlow_f(cs, c + 1))] += 1
    print(nm, len(data), 'bad', sum(1 for d in data if not d[2] or d[2][0] > d[2][1]), cnt.most_common(4))
    for act, _ in cnt.most_common(2):
        rows, lo, hi, P = [], [], [], []
        bad = 0
        for pt, cs, w in data:
            if not w or w[0] > w[1]:
                bad += 1
                continue
            w2 = actwin_f(cs, w, *act)
            if w2 is None:
                bad += 1
                continue
            Nn, uu, vv = pt
            rr, dd = 4 * uu - Nn, Nn - 1 - uu - 2 * vv
            f = [1, Nn, rr, dd]
            if quad:
                f += [rr * rr / 100, rr * dd / 100, dd * dd / 100, rr * 1000 / Nn, dd * 1000 / Nn, 1000 / Nn]
            rows.append(f)
            lo.append(w2[0]); hi.append(w2[1]); P.append((Nn, rr, dd))
        if bad:
            print('  act', act, 'bad', bad)
            continue
        X = np.array(rows, float)
        n = X.shape[1]
        A = np.vstack([np.hstack([-X, np.ones((len(X), 1))]), np.hstack([X, np.ones((len(X), 1))])])
        b = np.concatenate([-np.array(lo), np.array(hi)])
        res = linprog([0] * n + [-1], A_ub=A, b_ub=b, bounds=[(None, None)] * (n + 1), method='highs')
        if res.status != 0:
            print('  act', act, 'LP', res.status)
            continue
        c = res.x[:n]
        sl = res.x[n]
        val = X @ c
        marg = np.minimum(val - np.array(lo), np.array(hi) - val)
        idx = np.argsort(marg)[:5]
        print('  act', act, 'slack %.4f' % sl, 'coef', np.round(c, 4), 'tight', [P[i] for i in idx])


if __name__ == '__main__':
    run(sys.argv[1], len(sys.argv) > 2 and sys.argv[2] == 'quad')
