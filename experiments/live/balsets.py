"""balsets.py N c: subsets F of class c (c = 1 odds, 0 evens) that are balanced around
every panel of the other class."""
import sys
from itertools import combinations

N, c = int(sys.argv[1]), int(sys.argv[2])
cls = [x for x in range(1, N + 1) if x % 2 == c]
oth = [x for x in range(1, N + 1) if x % 2 != c]


def bal(F, m):
    r = min(m - 1, N - m)
    return sum(1 for x in F if m - r <= x < m) == sum(1 for x in F if m < x <= m + r)


for k in range(0, len(cls) + 1):
    for F in combinations(cls, k):
        if all(bal(F, m) for m in oth):
            print(k, F)
