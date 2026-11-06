#!/usr/bin/env python3
"""qpfit.py K [deg]: search a quasi-polynomial (degree deg, default K) of minimal period for the
number of copies of size K in [N] (data out/fitK.txt), fitting on N >= N0 and checking all
remaining points.  Prints the period and the leading coefficients."""
import sys, os
from fractions import Fraction as F

def solve(rows, rhs):
    n = len(rows[0]); M = [list(map(F, r)) + [F(b)] for r, b in zip(rows, rhs)]
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: return None
        M[r], M[p] = M[p], M[r]
        M[r] = [v / M[r][c] for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                M[i] = [a - M[i][c] * b for a, b in zip(M[i], M[r])]
        r += 1
    sol = [M[i][n] for i in range(n)]
    for i in range(n, len(M)):
        if M[i][n] != 0: return None
    return sol

def main():
    K = int(sys.argv[1]); deg = int(sys.argv[2]) if len(sys.argv) > 2 else K
    N0 = int(sys.argv[3]) if len(sys.argv) > 3 else 2 * K
    here = os.path.dirname(os.path.abspath(__file__))
    data = {}
    for l in open(os.path.join(here, 'out', 'fit%d.txt' % K)):
        n, k, c = map(int, l.split()); data[n] = c
    Ns = [n for n in sorted(data) if n >= N0]
    for p in range(1, 200):
        ok = True; polys = {}
        for r in range(p):
            pts = [n for n in Ns if n % p == r]
            if len(pts) < deg + 2: ok = False; break
            sol = solve([[n ** e for e in range(deg + 1)] for n in pts], [data[n] for n in pts])
            if sol is None: ok = False; break
            polys[r] = sol
        if ok:
            print('K=%d period %d (fitted on N >= %d, %d points)' % (K, p, N0, len(Ns)))
            lead = set(polys[r][deg] for r in polys)
            print('  leading coefficient(s):', lead)
            for e in range(deg, -1, -1):
                vals = [polys[r][e] for r in range(p)]
                per = next(q for q in range(1, p + 1) if p % q == 0 and all(vals[i] == vals[i % q] for i in range(p)))
                print('  coeff N^%d: period %d' % (e, per), vals[:min(per, 12)])
            # check small N
            bad = [n for n in sorted(data) if n < N0 and sum(polys[n % p][e] * n ** e for e in range(deg + 1)) != data[n]]
            print('  fails for N <', N0, ':', bad)
            return
    print('no period < 200')

main()
