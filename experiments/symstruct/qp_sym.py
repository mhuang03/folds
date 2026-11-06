"""qp_sym.py FILE DEG L: smallest period p | L of an exact quasi-polynomial of degree DEG
through the exact series in FILE (rows "N value"), and the Fourier-type decomposition of the
coefficients (for which N mod d each coefficient depends on)."""
import sys
from fractions import Fraction as F
import sympy as sp

x = sp.Symbol('N')
fn, deg, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
d = {int(a): int(b) for a, b in (l.split() for l in open(fn))}
NMIN = int(sys.argv[4]) if len(sys.argv) > 4 else 1


def fit(p):
    polys = {}
    for r in range(p):
        ns = [n for n in sorted(d) if n >= NMIN and n % p == r]
        P = sp.expand(sp.interpolate([(n, d[n]) for n in ns[:deg + 1]], x))
        if any(P.subs(x, n) != d[n] for n in ns[deg + 1:]):
            return None
        polys[r] = sp.Poly(P, x)
    return polys


for p in sorted(q for q in range(1, L + 1) if L % q == 0):
    polys = fit(p)
    if polys:
        print(f"period {p} (divides lcm {L}); checked on N = {NMIN}..{max(d)}")
        for j in range(deg, -1, -1):
            cs = [polys[r].coeff_monomial(x**j) for r in range(p)]
            # smallest period of this coefficient
            q = min(q for q in range(1, p + 1) if p % q == 0 and all(cs[r] == cs[r % q] for r in range(p)))
            show = cs[:q]
            print(f"  coeff of N^{j}: period {q}: {show if q <= 12 else str(show[:12]) + ' ...'}")
        if p <= 8:
            for r in range(p):
                print(f"  N = {r} mod {p}: {sp.factor(polys[r].as_expr())}")
        break
