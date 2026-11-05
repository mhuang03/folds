"""Layered quasi-polynomial fit: T(N) = sum_i c_i(N mod p_i) N^i, each coefficient with its
own period p_i (p_deg is usually 1).  Exact rational Gaussian elimination.

qfit.py FILE COL "p_deg,...,p_0"  (a period may be a sum like 8+3+5+7: additive periodic pieces) [NMIN]
Fits on all points with N >= NMIN; reports whether the system is consistent and has a
unique solution, how many equations were left over as checks, and the coefficients.
"""
import sys
from fractions import Fraction as F


def load(fn, col):
    d = {}
    for line in open(fn):
        t = line.split()
        if len(t) > col and t[0].isdigit():
            d[int(t[0])] = int(t[col])
    return d


def solve(rows, rhs, nvar):
    """Exact elimination. Returns (consistent, unique, solution or None)."""
    A = [list(map(F, r)) + [F(b)] for r, b in zip(rows, rhs)]
    piv = []
    r = 0
    for c in range(nvar):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [v * inv for v in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    consistent = all(A[i][-1] == 0 for i in range(r, len(A)))
    unique = len(piv) == nvar
    sol = None
    if consistent and unique:
        sol = [A[i][-1] for i in range(nvar)]
    return consistent, unique, sol, len(A) - r


def fit(d, periods, nmin=1):
    deg = len(periods) - 1
    idx = []
    for i, ps in enumerate(periods):
        e = deg - i
        for j, p in enumerate(ps):
            # additive pieces: residues 0 of the 2nd, 3rd, ... piece are dropped (redundant)
            for res in range(1 if j else 0, p):
                idx.append((e, p, res))
    rows, rhs = [], []
    for n in sorted(d):
        if n < nmin:
            continue
        rows.append([n ** e if n % p == res else 0 for (e, p, res) in idx])
        rhs.append(d[n])
    cons, uniq, sol, extra = solve(rows, rhs, len(idx))
    return cons, uniq, sol, extra, idx


def show(sol, idx):
    out = {}
    for (e, p, res), v in zip(idx, sol):
        out.setdefault((e, p), []).append(v)
    for (e, p) in sorted(out, key=lambda t: -t[0]):
        vs = out[(e, p)]
        print(f'  N^{e} [mod {p}]: ' + ', '.join(str(v) for v in vs))


if __name__ == '__main__':
    d = load(sys.argv[1], int(sys.argv[2]))
    periods = [[int(u) for u in t.split('+')] for t in sys.argv[3].split(',')]
    nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    cons, uniq, sol, extra, idx = fit(d, periods, nmin)
    print('N range', max(nmin, min(d)), '..', max(d), 'consistent', cons, 'unique', uniq,
          'spare equations (checks)', extra)
    if sol:
        show(sol, idx)
