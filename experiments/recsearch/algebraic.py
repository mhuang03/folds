"""Family 4: algebraic and differentially algebraic generating functions.

F = sum_{n>=0} a(n) x^n (OGF, a(0) = 1) and the EGF sum a(n) x^n/n!.
(Shifting F by a constant maps each ansatz class to itself, so a(0) does not matter.)

ALG(dx, df):   sum_{i<=dx, j<=df} c_ij x^i F^j = 0                (Pade-Hermite)
DA(ord, deg, dx):  sum over monomials m in F, F', ..., F^(ord) of total degree <= deg,
               and i <= dx, of c_{m,i} x^i m(F) = 0.
Equations: the coefficients of x^0..x^V, V = 37 - ord (the last exactly known
coefficient of every monomial).  K unknowns; all shapes with E >= K+5 are run.
Any non-zero solution would be genuine (no monomial combination vanishes identically).
"""
from itertools import combinations_with_replacement as cwr
from fractions import Fraction
from math import factorial
from common import A, NMAX, analyze, fmt


def mul(f, g, V):
    return [sum((f[k] * g[n - k] for k in range(n + 1)), Fraction(0)) for n in range(V + 1)]


def deriv(f):
    return [n * f[n] for n in range(1, len(f))]


def series(kind):
    f = [Fraction(1)] + [Fraction(A[n]) for n in range(1, NMAX + 1)]
    if kind == 'EGF':
        f = [x / factorial(n) for n, x in enumerate(f)]
    return f


def rows_from(polys, dx, V):
    """polys: list of truncated series (length >= V+1); unknowns c_{p,i} for x^i * p."""
    rows = []
    for n in range(V + 1):
        rows.append([p[n - i] if n - i >= 0 else Fraction(0) for p in polys for i in range(dx + 1)])
    return rows


def alg(kind, out):
    f = series(kind)
    V = NMAX
    pw = [[Fraction(1)] + [Fraction(0)] * V]
    for j in range(1, 40):
        pw.append(mul(pw[-1], f, V))
    E = V + 1
    for df in range(1, 33):
        for dx in range(0, 33):
            K = (dx + 1) * (df + 1)
            if K + 5 > E:
                continue
            res = analyze(rows_from(pw[:df + 1], dx, V))
            print(f"{kind} ALG dx={dx:2d} df={df:2d}  " + fmt(res), file=out, flush=True)
            yield ('ALG', kind, dx, df, res)


def da(kind, out):
    f = series(kind)
    ders = [f]
    for o in range(1, 4):
        ders.append(deriv(ders[-1]))
    for order in (1, 2, 3):
        V = NMAX - order
        E = V + 1
        base = [d[:V + 1] for d in ders[:order + 1]]
        for deg in (2, 3, 4):
            monos = [()]
            for d in range(1, deg + 1):
                monos += list(cwr(range(order + 1), d))
            ser = []
            for m in monos:
                s = [Fraction(1)] + [Fraction(0)] * V
                for k in m:
                    s = mul(s, base[k], V)
                ser.append(s)
            for dx in range(0, 20):
                K = len(monos) * (dx + 1)
                if K + 5 > E:
                    break
                res = analyze(rows_from(ser, dx, V))
                print(f"{kind} DA order={order} deg<={deg} dx={dx}  monomials={len(monos)}  " + fmt(res), file=out, flush=True)
                yield ('DA', kind, (order, deg), dx, res)


def main():
    import sys
    out = sys.stdout
    print(__doc__)
    summary = []
    for kind in ('OGF', 'EGF'):
        for gen in (alg(kind, out), da(kind, out)):
            n = 0
            mx = None
            rel = 0
            maxK = 0
            for fam, k, p, q, res in gen:
                n += 1
                maxK = max(maxK, res['K'])
                if res['kernel']:
                    rel += 1
                    print('   RELATION', fam, k, p, q, res['kernel'][:1])
                if mx is None or res['excess'] > mx[0]:
                    mx = (res['excess'], p, q)
            summary.append(f"{kind} {fam}: {n} shapes, max K={maxK}, relations={rel}, max excess={mx[0]:+d} at {mx[1]},{mx[2]}")
    print('\nSUMMARY')
    for s in summary:
        print(' ', s)


if __name__ == '__main__':
    main()
