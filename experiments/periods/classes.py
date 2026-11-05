"""classes.py KMAX: admissible order types (full-dimensional continuum polytopes), sigma forced
by the window rule; writes types_K.txt (one order type per line, ranks as digits/space-separated)
for every K <= KMAX (mirror pairs both present).  Interior test: LP Chebyshev radius > 1e-9 (as contpatterns.py)."""
import sys
import numpy as np
from scipy.optimize import linprog
from poly import rows, extensions


def interior(pi):
    R = rows(pi)
    K = len(pi)
    A = -np.array([a for a, c, s, t in R], float)   # -a.y <= c
    b = np.array([c for a, c, s, t in R], float)
    norms = np.linalg.norm(A, axis=1)
    res = linprog(np.r_[np.zeros(K), -1], A_ub=np.c_[A, norms], b_ub=b,
                  bounds=[(None, None)] * K + [(0, None)], method='highs')
    return res.status == 0 and res.x[-1] > 1e-9


if __name__ == '__main__':
    KMAX = int(sys.argv[1])
    cur = [(1,)]
    for K in range(2, KMAX + 1):
        nxt = [q for p in cur for q in extensions(p) if interior(q)]
        cur = nxt
        with open(f'types_{K}.txt', 'w') as f:
            for p in cur:
                f.write(' '.join(map(str, p)) + '\n')
        print(K, len(cur), flush=True)
