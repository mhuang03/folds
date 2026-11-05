"""copies2.py N: copies X (|X| >= 3) whose complement is reachable from scratch.
Copies are built incrementally (a subset of a copy's enumeration need not be a copy, so we
just enumerate all subsets with pruning on the copy condition for the first elements)."""
import sys
from functools import lru_cache
from itertools import combinations
from splits import is_copy

N = int(sys.argv[1])


def ok(S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
        sum(1 for d in range(1, r + 1) if (m + d) in S)


@lru_cache(None)
def reach_from_scratch(S):
    # S reachable from empty: remove a last element x valid w.r.t. S - x
    if not S:
        return True
    return any(ok(S - {x}, x) and reach_from_scratch(S - {x}) for x in S)


for p in range(3, N):
    for X in combinations(range(1, N + 1), p):
        if not is_copy(N, X):
            continue
        Y = frozenset(range(1, N + 1)) - set(X)
        if reach_from_scratch(Y):
            par = "".join("e" if x % 2 == 0 else "o" for x in X)
            print(p, X, par, "Ycopy" if is_copy(N, tuple(sorted(Y))) else "")
