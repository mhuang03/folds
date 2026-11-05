"""Analyse the statistic generating polynomials from stats_out.txt:
palindromic?, real-rooted?, factorization over Q, gamma-positivity (for palindromic ones)."""
import sys
from sympy import symbols, Poly, factor_list, real_roots, gcd as sgcd
import numpy as np

t = symbols('t')
data = {}
N = None
for line in open(sys.argv[1] if len(sys.argv) > 1 else "stats_out.txt"):
    w = line.split()
    if w[0] == "N":
        N = int(w[1]); data[N] = {}
        continue
    name = w[0].rstrip(':')
    data[N][name] = [int(x) for x in w[1:]]


def trim(c):
    lo = 0
    while lo < len(c) and c[lo] == 0:
        lo += 1
    hi = len(c)
    while hi > lo and c[hi - 1] == 0:
        hi -= 1
    return lo, c[lo:hi]


def gamma(c):
    """gamma vector of a palindromic polynomial with coeff list c (degree d)."""
    c = list(c); d = len(c) - 1; g = []
    while len(c) > 0 and any(c):
        dd = len(c) - 1
        gi = c[0]; g.append(gi)
        # subtract gi * t^i (1+t)^(d-2i), here relative: gi*(1+t)^dd
        from math import comb
        c = [c[j] - gi * comb(dd, j) for j in range(dd + 1)]
        c = c[1:-1] if dd >= 2 else []
    return g


for name in ["pos1", "first", "free", "full", "zero", "des", "cross", "lrmax", "inv", "mid"]:
    print("=" * 10, name)
    for N in sorted(data):
        if name not in data[N] or N < 3:
            continue
        lo, c = trim(data[N][name])
        if len(c) <= 1:
            print(N, "shift", lo, c); continue
        pal = c == c[::-1]
        p = Poly(sum(ci * t**i for i, ci in enumerate(c)), t)
        nreal = len(real_roots(p)) if p.degree() <= 60 else -1
        rr = nreal == p.degree()
        fl = factor_list(p)
        facs = [(str(f.as_expr()) if f.degree() <= 3 else f"deg{f.degree()}", e) for f, e in fl[1]]
        g = gamma(c) if pal else None
        print(N, f"shift={lo}", c, "PAL" if pal else "", "REALROOTED" if rr else f"real={nreal}/{p.degree()}",
              "content", fl[0], facs, ("gamma=" + str(g)) if g else "")
