"""fitc0.py: for a thin line and a slice option, the exact c0-windows along the line, and an LP fit
of a linear c0 = a + b u + g N inside all windows (maximising the minimal slack).
usage: python3 fitc0.py cls off o f t p j [Nlist]"""
import sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from slicelib import cons, window


def line_points(cls, off, N):
    out = []
    for u in range(4, N):
        v = u + off if cls == 1 else 2 * u + off
        if v < u or u + 2 * v + 1 > N:
            continue
        if (u + v - N) % 2:
            continue
        if cls == 2 and (N > 8 * u + 320 or v < u + 10):
            continue
        if cls == 1 and off == 1 and u >= 5 and 3 * u + 21 <= N:
            continue
        out.append((u, v))
    return out


def windows(cls, off, opt, Ns):
    res = []
    for N in Ns:
        for u, v in line_points(cls, off, N):
            w = window(cons(N, u, v, opt, exact_smax=False))
            res.append((N, u, v, w))
    return res


def fit(res, feats=lambda N, u: [1, u, N]):
    rows, bl, bh = [], [], []
    for N, u, v, w in res:
        if w is None or w[0] > w[1]:
            return None
        rows.append(feats(N, u))
        bl.append(float(w[0]))
        bh.append(float(w[1]))
    X = np.array(rows, float)
    k = X.shape[1]
    # vars: coeffs (k), t (slack, maximise).  lo + t <= X c <= hi - t
    A, b = [], []
    for i in range(len(rows)):
        A.append(list(-X[i]) + [1.0]); b.append(-bl[i])
        A.append(list(X[i]) + [1.0]); b.append(bh[i])
    r = linprog([0] * k + [-1], A_ub=A, b_ub=b, bounds=[(None, None)] * k + [(None, None)], method='highs')
    if r.status != 0:
        return None
    return r.x[:k], r.x[k]


if __name__ == '__main__':
    cls, off, o, f, t, p, j = map(int, sys.argv[1:8])
    Ns = [int(x) for x in sys.argv[8].split(',')] if len(sys.argv) > 8 else [301, 302, 401, 402, 1001, 1002, 3001, 3000]
    res = windows(cls, off, (o, f, t, p, j), Ns)
    bad = [(N, u) for N, u, v, w in res if w is None or w[0] > w[1]]
    print('points', len(res), 'bad', bad[:20], len(bad))
    good = [r for r in res if not (r[3] is None or r[3][0] > r[3][1])]
    print(fit(good))
    for N, u, v, w in good[:: max(1, len(good) // 15)]:
        print(N, u, v, float(w[0]), float(w[1]), float(w[1] - w[0]))
