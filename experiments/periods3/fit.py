"""fit.py FILE F DEG [MMIN]: fit (-1)^(m+1) * A * D^F (A = A_above, A_below) as
sum_{i<=F, j<=DEG} c_ij m^j D^(F-i)... i.e. a polynomial in m and D, exactly over Q; report the
fit from the first points and check it on the rest."""
import sys
from fractions import Fraction as Fr
import sympy as sp

fn, F, DEG = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
MMIN = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rows = []
for line in open(fn):
    m, a, b = line.split()
    m = int(m)
    if m < MMIN:
        continue
    rows.append((m, Fr(a), Fr(b)))
mm = sp.Symbol('m')
DD = sp.Symbol('D')
for col, name in ((1, 'A_above'), (2, 'A_below')):
    basis = [(i, j) for i in range(F + 1) for j in range(DEG + 1)]
    nb = len(basis)
    if len(rows) < nb + 1:
        print('not enough data', len(rows), nb)
        sys.exit()
    def val(r):
        m = r[0]
        D = 2 ** (m - 1) - 1
        return (-1) ** (m + 1) * r[col] * D ** F
    A = sp.Matrix([[sp.Integer(r[0]) ** j * sp.Integer(2 ** (r[0] - 1) - 1) ** (F - i) for (i, j) in basis] for r in rows[:nb]])
    y = sp.Matrix([sp.Rational(val(r).numerator, val(r).denominator) for r in rows[:nb]])
    c = A.LUsolve(y)
    expr = sum(c[t] * mm ** basis[t][1] * DD ** (F - basis[t][0]) for t in range(nb))
    ok = True
    for r in rows[nb:]:
        m = r[0]
        D = 2 ** (m - 1) - 1
        pred = expr.subs({mm: m, DD: D})
        v = val(r)
        if pred != sp.Rational(v.numerator, v.denominator):
            ok = False
            print(f'  {name}: mismatch at m={m}: pred {pred} got {v}')
    print(f'{name}: (-1)^(m+1) A D^{F} = {sp.factor(sp.expand(expr))}   [checked on {len(rows) - nb} extra points: {ok}]')
    print('   collected:', sp.collect(sp.expand(expr), DD))
