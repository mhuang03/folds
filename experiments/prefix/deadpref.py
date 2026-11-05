"""deadpref.py N k: list the valid k-prefixes that cannot be completed (small N)."""
import sys
from functools import lru_cache
from itertools import permutations

N, k = int(sys.argv[1]), int(sys.argv[2])


def ok(S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S)


@lru_cache(None)
def completable(S):
    if len(S) == N:
        return True
    return any(completable(S | {m}) for m in range(1, N + 1) if m not in S and ok(S, m))


for p in permutations(range(1, N + 1), k):
    if all(ok(frozenset(p[:i]), p[i]) for i in range(k)) and not completable(frozenset(p)):
        print(p)
