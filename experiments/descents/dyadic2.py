"""For valid a, the dyadic first-occurrence projections d_j (see dyadic.py).  Check whether
LDS(d_j) >= lg(M_j) and des(d_j) >= lg(M_j) - 1 for all j (M_j = floor(M/2^j))."""
from common import *
from dyadic import dj
import sys
from collections import Counter
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1; c = Counter()
    for a in A:
        a = list(a)
        for j in range(lg(M)):
            d = dj(a, M, j); Mj = M >> j
            c[(j, lds(d) - lg(Mj), des(d) - (lg(Mj) - 1))] += 0
            if lds(d) < lg(Mj): c[('ldsfail', j)] += 1
            if des(d) < lg(Mj) - 1: c[('desfail', j)] += 1
    print(N, {k: v for k, v in c.items() if v})
