"""Exact quasi-polynomial fitting.

fit.py FILE COL DEG [NMIN]
FILE has rows "N v1 v2 ...". COL is the 1-based column index after N.
For each candidate period p, fit, for each residue class N = r (mod p), a polynomial of
degree DEG through the first DEG+1 points with N >= NMIN (exact rational interpolation),
and check it on all the remaining points of that class.  Prints the smallest period that
works, the number of held-out checks, and the polynomials.
"""
import sys
from fractions import Fraction as F
import sympy as sp

x = sp.Symbol('N')


def load(fn, col):
    d = {}
    for line in open(fn):
        t = line.split()
        if len(t) > col and t[0].isdigit():
            d[int(t[0])] = int(t[col])
    return d


def interp(pts):
    return sp.expand(sp.interpolate([(a, b) for a, b in pts], x))


def try_period(d, deg, p, nmin):
    polys = {}
    checks = 0
    for r in range(p):
        ns = sorted(n for n in d if n >= nmin and n % p == r)
        if len(ns) < deg + 2:
            return None
        pts = [(n, d[n]) for n in ns[:deg + 1]]
        P = interp(pts)
        for n in ns[deg + 1:]:
            if P.subs(x, n) != d[n]:
                return None
            checks += 1
        polys[r] = P
    return polys, checks


def best(d, deg, nmin=1, pmax=64):
    for p in range(1, pmax + 1):
        res = try_period(d, deg, p, nmin)
        if res:
            return p, res
    return None


if __name__ == '__main__':
    fn, col, deg = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    d = load(fn, col)
    print('data N =', min(d), '..', max(d))
    r = best(d, deg, nmin)
    if not r:
        print('no period <= 64 works')
        sys.exit()
    p, (polys, checks) = r
    print('period', p, 'held-out checks', checks)
    for k, P in polys.items():
        print(f'  N = {k} mod {p}:', sp.factor(P) if deg <= 3 else P)
