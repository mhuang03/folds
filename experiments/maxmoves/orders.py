"""orders.py -- valid orders of a set S (prefixes of fold sequences) and V(S).
usage: python3 orders.py N x1 x2 ..."""
import sys
from itertools import permutations

def semi(N, S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S)

N = int(sys.argv[1]); S = [int(v) for v in sys.argv[2:]]
V = [m for m in range(1, N + 1) if m not in S and semi(N, set(S), m)]
print("V =", len(V), "valid:", V)
for p in permutations(S):
    if all(semi(N, set(p[:i]), p[i]) for i in range(len(p))):
        print("valid order:", list(p))
