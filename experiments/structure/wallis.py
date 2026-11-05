"""Single-constraint probability and the 'independent constraints' (Wallis) model.

For a uniformly random permutation, the constraint at a panel with radius r holds with
probability p(r) = (2r)!! / (2r+1)!! = 4^r r!^2 / (2r+1)!   (verified below by exact counting).
Model:  a_W(N) = N! * prod_m p(r_m),  r_m = min(m-1, N-m)."""
from fractions import Fraction
from math import comb, factorial
from common import A, g_array
import math

def p(r):
    return Fraction(4 ** r * factorial(r) ** 2, factorial(2 * r + 1))

def p_direct(r):
    # rank of m among its window is uniform in 0..2r; given j earlier elements, P(balanced)
    return sum(Fraction(comb(r, i) ** 2, comb(2 * r, 2 * i)) for i in range(r + 1)) / (2 * r + 1)

for r in range(8):
    assert p(r) == p_direct(r)
# check with the 'one' mode of dp: only panel m constrained
for N in range(3, 12):
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        v = int(g_array(N, "one", m)[(1 << N) - 1])
        assert Fraction(v, factorial(N)) == p(r), (N, m)
print("p(r) = (2r)!!/(2r+1)!! verified (and single-panel mode of dp.c for N<=11)")

print("N a(N) a_W(N) ratio ratio^(1/N)")
for N in range(1, len(A) + 1):
    w = Fraction(factorial(N))
    for m in range(1, N + 1): w *= p(min(m - 1, N - m))
    rt = A[N - 1] / float(w)
    print(N, A[N - 1], "%.5g" % float(w), "%.4f" % rt, "%.4f" % rt ** (1 / N))
