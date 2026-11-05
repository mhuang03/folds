"""Real-rootedness / palindromicity / gamma-positivity of polynomials in polydp_out.txt."""
from math import comb
from sympy import symbols, Poly, real_roots
from data import a

t = symbols('t')


def gamma(c):
    c = list(c); g = []
    while c and any(c):
        dd = len(c) - 1; gi = c[0]; g.append(gi)
        c = [c[j] - gi * comb(dd, j) for j in range(dd + 1)]
        c = c[1:-1] if dd >= 2 else []
    return g


def lc_ok(c):
    return all(c[i] * c[i] >= c[i - 1] * c[i + 1] for i in range(1, len(c) - 1))


for line in open("polydp_out.txt"):
    w = line.split(); N = int(w[0]); mode = w[1]; co = [int(x) for x in w[2:]]
    assert sum(co) == a[N], (N, mode)
    lo = next(i for i, x in enumerate(co) if x)
    hi = max(i for i, x in enumerate(co) if x)
    c = co[lo:hi + 1]
    if len(c) == 1:
        print(N, mode, "monomial t^%d" % lo); continue
    p = Poly(sum(ci * t**i for i, ci in enumerate(c)), t)
    rr = len(real_roots(p)) == p.degree()
    pal = c == c[::-1]
    gm = gamma(c) if pal else None
    print(N, mode, f"t^{lo}*", c, "PAL" if pal else "", "real-rooted" if rr else "NOT real-rooted",
          "" if lc_ok(c) else "NOT log-concave",
          ("gamma>=0" if all(x >= 0 for x in gm) else f"gamma has negatives {gm}") if pal else "")
