"""Independence heuristic: at step k, assume the k-1 earlier panels form a uniformly random set.
Then the expected number of valid moves is
   nu(N,k) = sum_m P(m not in S) P(balanced | m not in S)
and the model is  a~(N) = prod_k nu(N,k)  (= N! prod q_rand).  Compare with a(N)."""
import math
from math import comb
from fractions import Fraction
from common import A

def nu(N, k):
    # S uniform among (k-1)-subsets of [N]
    tot = Fraction(0)
    s = k - 1
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        # m not in S: S is an s-subset of the other N-1
        pnot = Fraction(comb(N - 1, s), comb(N, s))
        bal = Fraction(sum(comb(r, i) ** 2 * comb(N - 1 - 2 * r, s - 2 * i) for i in range(0, r + 1) if s - 2 * i >= 0),
                       comb(N - 1, s))
        tot += pnot * bal
    return tot

print("N a(N) model ratio ratio^(1/N)")
prev = None
for N in range(1, len(A) + 1):
    mod = Fraction(1)
    for k in range(1, N + 1): mod *= nu(N, k)
    ratio = A[N - 1] / float(mod)
    print(N, A[N - 1], "%.4g" % float(mod), "%.4f" % ratio, "%.4f" % ratio ** (1 / N))
