"""beatty.py N1 N2: Beatty sets X(N,p,g) = {floor((r N + g) / p) : r = 1..p}; report which are
window copies and whether their complement is reachable from scratch."""
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

    res = []
    for p in range(2, N):
        for g in range(-N + 1, 1):
            X = tuple((r * N + g) // p for r in range(1, p + 1))
            if X[0] < 1 or len(set(X)) < p:
                continue
            if not is_copy(N, X):
                continue
            Y = frozenset(range(1, N + 1)) - set(X)
            res.append((p, g, X, rfs(Y)))
    return res


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for p, g, X, ry in run(N):
        print(N, p, g, X, "Yreach" if ry else "-")
