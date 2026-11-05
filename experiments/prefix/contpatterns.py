"""contpatterns.py KMAX [vol]: enumerate the full-dimensional (order type, sign matrix) classes
in the CONTINUUM (no N cut-off), by extending admissible classes of length k-1 with a new
point (rank insertion + a balanced choice of which earlier points lie in its window), keeping
those whose polytope has an interior point (LP Chebyshev radius > 1e-9).
Reports, per k: number of classes, number of distinct order types, and whether any order type
carries two classes.  With 'out', writes the classes for K = KMAX to cpK.txt (input for volumes.py)."""
import sys
from itertools import combinations
import numpy as np
from scipy.optimize import linprog

KMAX = int(sys.argv[1])
want_vol = len(sys.argv) > 2


def ineqs(K, pi, sig):
    R = []

    def row(coef, b):
        a = [0] * K
        for i, c in coef:
            a[i] += c
        R.append((a, b))
    for i in range(K):
        row([(i, -1)], 0)
        row([(i, 1)], 1)
    order = sorted(range(K), key=lambda i: pi[i])
    for u, v in zip(order, order[1:]):
        row([(u, 1), (v, -1)], 0)
    for (i, j), s in sig.items():
        up = pi[j] > pi[i]
        if s == 1:
            row([(j, 2), (i, -1)], 1)
        elif s == -1:
            row([(j, -2), (i, 1)], 0)
        elif up:
            row([(j, -2), (i, 1)], -1)
        else:
            row([(j, 2), (i, -1)], 0)
    return R


def interior(K, R):
    A = np.array([a for a, b in R], float)
    b = np.array([b for a, b in R], float)
    norms = np.linalg.norm(A, axis=1)
    res = linprog(np.r_[np.zeros(K), -1], A_ub=np.c_[A, norms], b_ub=b,
                  bounds=[(None, None)] * K + [(0, None)], method='highs')
    return res.status == 0 and res.x[-1] > 1e-9


classes = [((1,), {})]
for K in range(2, KMAX + 1):
    new = []
    for pi, sig in classes:
        for r in range(1, K + 1):  # rank of the new point among K
            npi = tuple(p + (p >= r) for p in pi) + (r,)
            below = [i for i in range(K - 1) if npi[i] < r]
            above = [i for i in range(K - 1) if npi[i] > r]
            for t in range(0, min(len(below), len(above)) + 1):
                for B in combinations(below, t):
                    for A in combinations(above, t):
                        s = dict(sig)
                        for i in range(K - 1):
                            s[(i, K - 1)] = 1 if i in B else (-1 if i in A else 0)
                        if interior(K, ineqs(K, npi, s)):
                            new.append((npi, s))
    classes = new
    types = {}
    for pi, s in classes:
        types.setdefault(pi, []).append(s)
    multi = sum(1 for v in types.values() if len(v) > 1)
    print(f'k={K}: {len(classes)} full-dimensional classes, {len(types)} order types, '
          f'{multi} order types with more than one class', flush=True)

if want_vol:
    # write the classes in pieces.c format ("N key count") for volumes.py
    K = KMAX
    with open(f'cp{K}.txt', 'w') as f:
        for pi, s in classes:
            code = 0
            for i in range(K):
                code = code * (K - i) + sum(1 for j in range(i + 1, K) if pi[j] < pi[i])
            sc = 0
            for j in range(1, K):
                for i in range(j):
                    sc = sc * 3 + s[(i, j)] + 1
            f.write(f'0 {code * 3 ** (K * (K - 1) // 2) + sc} 1\n')
    print('wrote', f'cp{K}.txt')
