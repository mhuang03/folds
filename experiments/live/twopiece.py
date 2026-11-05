"""twopiece.py N1 N2: sets X = (class c on [1,k]) + (class 1-c on [k+1,N]); report those that
are copies, whether the complement is a copy / reachable from scratch."""
import sys
from functools import lru_cache
from splits import is_copy


def run(N):
    def ok(S, m):
        r = min(m - 1, N - m)
        return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
            sum(1 for d in range(1, r + 1) if (m + d) in S)

    @lru_cache(None)
    def rfs(S):
        if not S:
            return True
        return any(ok(S - {x}, x) and rfs(S - {x}) for x in S)

    for c in (0, 1):
        for k in range(0, N + 1):
            X = tuple(x for x in range(1, N + 1)
                      if (x <= k and x % 2 == c) or (x > k and x % 2 != c))
            Y = tuple(x for x in range(1, N + 1) if x not in X)
            cx, cy = is_copy(N, X), is_copy(N, Y)
            if cx or cy:
                print(N, "c", c, "k", k, "|X|", len(X), "Xcopy" if cx else "", "Ycopy" if cy else "",
                      "Xreach" if rfs(frozenset(X)) else "", "Yreach" if rfs(frozenset(Y)) else "")


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    run(N)
