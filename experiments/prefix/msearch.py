"""msearch.py FILE COL NMIN CANDS: fast consistency screen of layered/additive quasi-polynomial
period specs, by Gaussian elimination modulo a prime (p = 2^31-1).  CANDS is a python list of
per-coefficient candidate lists (top degree first), e.g. "[['1'],['1','2'],['4+3','24+7']]".
Prints only the specs that are consistent mod p with a unique solution (then confirm with qfit.py).
"""
import itertools
import sys
from qfit import load

P = 2147483647


def rank_consistent(rows, rhs):
    import numpy as np
    A = np.array([r + [b] for r, b in zip(rows, rhs)], dtype=object)
    A = np.array([[int(v) % P for v in row] for row in A], dtype=np.int64)
    m, n1 = A.shape
    n = n1 - 1
    r = 0
    for c in range(n):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            return False, False
        p = r + nz[0]
        A[[r, p]] = A[[p, r]]
        inv = pow(int(A[r, c]), P - 2, P)
        A[r] = (A[r] * inv) % P
        col = A[:, c].copy()
        col[r] = 0
        nzr = np.nonzero(col)[0]
        for i in nzr:
            A[i] = (A[i] - col[i] * A[r]) % P
        r += 1
    return bool(np.all(A[r:, n] == 0)), True


def build(d, periods, nmin):
    deg = len(periods) - 1
    idx = []
    for i, ps in enumerate(periods):
        e = deg - i
        for j, p in enumerate(ps):
            for res in range(1 if j else 0, p):
                idx.append((e, p, res))
    rows, rhs = [], []
    for n in sorted(d):
        if n >= nmin:
            rows.append([pow(n, e, P) if n % p == res else 0 for (e, p, res) in idx])
            rhs.append(d[n])
    return rows, rhs, len(idx)


if __name__ == '__main__':
    d = load(sys.argv[1], int(sys.argv[2]))
    nmin = int(sys.argv[3])
    cands = eval(sys.argv[4])
    for spec in itertools.product(*cands):
        periods = [[int(u) for u in t.split('+')] for t in spec]
        rows, rhs, nv = build(d, periods, nmin)
        if nv >= len(rows):
            continue
        cons, uniq = rank_consistent(rows, rhs)
        if cons and uniq:
            print(','.join(spec), 'unknowns', nv, 'equations', len(rows), flush=True)
