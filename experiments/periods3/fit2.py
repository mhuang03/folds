"""fit2.py FILE COL F DEG [PAR] [MMIN]: exact fit of (-1)^(m+1) A 4^... for chain weights:
y(m) = (-1)^(m+1) * A * X^F with X = 2^m, as sum_{i<=F, j<=DEG} c_ij m^j X^(F-i)
(+ if PAR=1, extra terms (-1)^m m^j X^(F-i) for i >= 1), fitted on the first points and checked
on the rest.  COL = 1, 2, 3 (A1, A2, A3 in chainW_F*.txt)."""
import sys
from fractions import Fraction as Fr
import sympy as sp

fn, col, F, DEG = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
PAR = int(sys.argv[5]) if len(sys.argv) > 5 else 0
MMIN = int(sys.argv[6]) if len(sys.argv) > 6 else 0
rows = []
for line in open(fn):
    p = line.split()
    if int(p[0]) >= MMIN:
        rows.append((int(p[0]), Fr(p[col])))
mm, XX, SS = sp.symbols('m X s')
basis = [(i, j, 0) for i in range(F + 1) for j in range(DEG + 1)]
if PAR:
    basis += [(i, j, 1) for i in range(1, F + 1) for j in range(DEG + 1)]
nb = len(basis)
print(f'{len(rows)} points, {nb} unknowns')
if len(rows) <= nb:
    sys.exit()


def b(r, t):
    m = r[0]
    i, j, par = t
    return sp.Integer(m) ** j * sp.Integer(2 ** m) ** (F - i) * ((-1) ** m if par else 1)


def y(r):
    m = r[0]
    v = (-1) ** (m + 1) * r[1] * 2 ** (m * F)
    return sp.Rational(v.numerator, v.denominator)


A = sp.Matrix([[b(r, t) for t in basis] for r in rows[:nb]])
c = A.LUsolve(sp.Matrix([y(r) for r in rows[:nb]]))
ok = all(sum(c[k] * b(r, basis[k]) for k in range(nb)) == y(r) for r in rows[nb:])
expr = sum(c[k] * mm ** basis[k][1] * XX ** (F - basis[k][0]) * (SS if basis[k][2] else 1) for k in range(nb))
print(f'(-1)^(m+1) A X^{F} = {sp.collect(sp.expand(expr), [XX, SS])}   (s = (-1)^m, X = 2^m)')
print(f'checked on {len(rows) - nb} held-out points: {ok}')
