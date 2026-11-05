"""verts.py k: denominators of all vertices in [0,1]^k of the hyperplane arrangement
   x_j = 0, x_j = 1, x_j = x_i, 2 x_j = x_i, 2 x_j = x_i + 1   (i != j)
which bounds the chambers on which the continuous validity pattern is constant.
(In the discrete count the hyperplanes are 2x_j = x_i + {0,1,2}, 2x_j = x_i + N + {0,1}.)
Prints the set of vertex denominators and their lcm (an upper bound for the
quasi-period of T(N,k) and V(N,k), heuristically)."""
import itertools
import sys
from fractions import Fraction as F
from math import lcm


def solve(rows):
    k = len(rows)
    A = [list(map(F, r)) for r in rows]
    for c in range(k):
        p = next((i for i in range(c, k) if A[i][c] != 0), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        inv = 1 / A[c][c]
        A[c] = [v * inv for v in A[c]]
        for i in range(k):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return [A[i][-1] for i in range(k)]


k = int(sys.argv[1])
ordered = len(sys.argv) > 2  # only hyperplanes comparing x_j with earlier x_i (i < j)
H = []  # rows: coefficients (k) + rhs
for j in range(k):
    e = [0] * k
    e[j] = 1
    H.append(e + [0])
    H.append(e + [1])
    for i in range(k):
        if i == j or (ordered and i > j):
            continue
        r = [0] * k
        r[j] = 2
        r[i] = -1
        H.append(r + [0])
        H.append(r + [1])
        r = [0] * k
        r[j] = 1
        r[i] = -1
        H.append(r + [0])
H = [list(t) for t in set(tuple(h) for h in H)]
dens = {}
for comb in itertools.combinations(H, k):
    v = solve([list(h) for h in comb])
    if v is None or not all(0 <= t <= 1 for t in v):
        continue
    d = lcm(*[t.denominator for t in v])
    dens[d] = dens.get(d, 0) + 1
print(sorted(dens.items()), 'lcm =', lcm(*dens))
