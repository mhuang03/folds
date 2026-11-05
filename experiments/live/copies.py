"""copies.py N: all window copies X (increasing enumeration is a window embedding of the
|X|-strip), and the weak splits [1..N] = X + Y with both parts copies (no balance needed:
X first, then Y reversed)."""
import sys
from itertools import combinations
from splits import is_copy

N = int(sys.argv[1])
cop = set()
for p in range(1, N + 1):
    for X in combinations(range(1, N + 1), p):
        if is_copy(N, X):
            cop.add(X)
print("copies", len(cop))
for X in sorted(cop, key=len):
    if 1 < len(X) < N:
        print(X)
print("weak splits")
for X in sorted(cop):
    Y = tuple(x for x in range(1, N + 1) if x not in X)
    if Y in cop and X < Y:
        print(X, Y)
