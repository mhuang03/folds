#!/usr/bin/env python3
"""Compare B(N) (balanced tournaments) with a(N) and with the independent ("Wallis product")
model  Bprod(N) = 2^C(N,2) * prod_m C(2 r_m, r_m) / 4^{r_m}.

Also reports, per N, whether the mutual graph G2 (x<y with x in W(y) and y in W(x)) is a
forest: the product formula is exact iff the dependency structure is a forest (see NOTES).
usage: analyze_B.py [variant]   (reads B_<variant>.txt)
"""
import sys
from math import comb, factorial
from fractions import Fraction
from sympy import factorint
from btour import arms

variant = sys.argv[1] if len(sys.argv) > 1 else 'true'
a = [int(l.split()[1]) for l in open('../semi_counts.txt') if l[0] != '#']
B = [int(l.split()[1]) for l in open(f'B_{variant}.txt')]

def forest(N, L, R):
    # union-find on mutual pairs
    par = list(range(N + 1))
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for x in range(1, N + 1):
        for y in range(x + 1, N + 1):
            if x in L[y] and y in R[x]:
                fx, fy = find(x), find(y)
                if fx == fy: return False
                par[fx] = fy
    return True

print(f"# variant {variant}")
print("# N  B(N)  v2(B)  odd-part-factorisation  B/Bprod  forest?  [a/N!]/[B/2^C]")
for N in range(1, len(B) + 1):
    L, R = arms(N, variant)
    b = B[N - 1]
    prod = Fraction(2 ** comb(N, 2))
    for m in range(1, N + 1):
        r = len(R[m])
        prod *= Fraction(comb(2 * r, r), 4 ** r)
    ratio = Fraction(b, 1) / prod if prod else None
    f = factorint(b, limit=10 ** 6) if b else {}
    v2 = f.pop(2, 0)
    odd = ' '.join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(f.items()))
    rho = (Fraction(a[N - 1], factorial(N)) / Fraction(b, 2 ** comb(N, 2))) if variant == 'true' and b else None
    print(N, b, v2, '[' + odd + ']', f"{float(ratio):.6f}" if ratio is not None else '-', ratio if ratio is not None and ratio.denominator < 10 ** 6 else '',
          'forest' if forest(N, L, R) else 'cyclic', f"{float(rho):.4f}" if rho is not None else '')
