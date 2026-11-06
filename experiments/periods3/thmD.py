"""thmD.py: the dominance inequalities of PROOFS.txt sections 3-4 (Theorems D1, D2).

Orbit family (order D = 2^n - 1, n = m - 1) in c_f of T(N, m + f):
    nonzero if   2 cos(pi/D) |Delta_0| > W R(n),     W = C(m+f, f),
    Delta_0 = A_above(1/D) - A_below(1/D), rotations 2^i/D carry no weight (Lemmas 2.3, 4.1).
Chain family (order 2^n) in c_f of T(N, m + f):
    nonzero if   |A1 + (-1)^(n+1) A3| > W Rc(n),
    A1 = A(1 0^(n-1)), A3 = A(1^n) (Lemma 2.4/2.5, Prop. 2.6).
R(n), Rc(n): numerically (rest.py) for n <= 24, the rigorous bounds Bo(n), Bc(n) beyond.
f = 1: closed forms (proved).  f = 2: exact values w1D_F2.txt, chainW_F2.txt (computed).
"""
from fractions import Fraction as Fr
from math import comb, cos, pi
import rest

RNUM = {}
RCNUM = {}


def R(n):
    if n <= 24:
        if n not in RNUM:
            RNUM[n] = rest.orbit_R(n)
        return RNUM[n], 'num'
    return rest.Bo(n), 'Bo'


def Rc(n):
    if n <= 24:
        if n not in RCNUM:
            RCNUM[n] = rest.chain_R(n)
        return RCNUM[n], 'num'
    return rest.Bc(n), 'Bc'


def orbit_f1(m):
    D = 2 ** (m - 1) - 1
    Aab = Fr((-1) ** (m + 1) * ((m - 7) * D - (m - 9)), 4 * D)
    Abe = Fr((-1) ** m, 2 * D)
    return Aab, Abe


def chain_f1(m):
    A1 = (-1) ** (m + 1) * (Fr(m - 7, 4) + Fr(3, 2 ** m))
    e = -5 if m % 2 == 0 else 1
    A3 = (-1) ** (m + 1) * (Fr(m + 4, 8) + Fr(e, 2 ** m))
    return A1, A3


def load(fn):
    d = {}
    try:
        for line in open(fn):
            p = line.split()
            d[int(p[0])] = [Fr(x) for x in p[1:]]
    except FileNotFoundError:
        pass
    return d


def check(f, mrange, orbit, chain, mmin_orbit):
    print(f'--- f = {f} ---')
    print('  m   orbit: 2cos|Delta0|   W*R(n)        ok | chain: |A1+-A3|   W*Rc(n)      ok')
    for m in mrange:
        n = m - 1
        D = 2 ** n - 1
        W = comb(m + f, f)
        s = f'{m:3d}  '
        o = orbit(m)
        if o is not None and m >= mmin_orbit:
            Aab, Abe = o
            lhs = 2 * cos(pi / D) * abs(float(Aab - Abe))
            r, how = R(n)
            s += f'{lhs:12.4e}  {W * r:12.4e}({how})  {"OK" if lhs > W * r else "--"} |'
        else:
            s += ' ' * 39 + '|'
        c = chain(m)
        if c is not None:
            A1, A3 = c
            lhs = abs(float(A1 + (-1) ** (n + 1) * A3))
            r, how = Rc(n)
            s += f' {lhs:12.4e}  {W * r:12.4e}({how})  {"OK" if lhs > W * r else "--"}'
        print(s, flush=True)


if __name__ == '__main__':
    check(1, list(range(4, 31)) + [40, 60, 100], orbit_f1, chain_f1, 6)
    o2 = load('w1D_F2.txt')
    c2 = load('chainW_F2.txt')
    check(2, range(4, 21), lambda m: tuple(o2[m]) if m in o2 else None,
          lambda m: (c2[m][0], c2[m][2]) if m in c2 else None, 7)
