"""nearclass.py N1 N2: copies X of size floor(N/2) or ceil(N/2) whose complement is reachable
from scratch (or a copy); print X as (class, removed, added)."""
import sys
from functools import lru_cache
from itertools import combinations
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

    ev = {x for x in range(1, N + 1) if x % 2 == 0}
    od = {x for x in range(1, N + 1) if x % 2 == 1}
    for p in sorted({N // 2, (N + 1) // 2}):
        # only sets within symmetric difference <= 4 of a class
        for base, nm in ((ev, "E"), (od, "O")):
            if len(base) != p:
                continue
            other = set(range(1, N + 1)) - base
            for k in range(0, 3):
                for rem in combinations(sorted(base), k):
                    for add in combinations(sorted(other), k):
                        X = tuple(sorted((base - set(rem)) | set(add)))
                        if not is_copy(N, X):
                            continue
                        Y = frozenset(range(1, N + 1)) - set(X)
                        if rfs(Y):
                            print(N, nm, "-", rem, "+", add,
                                  "Ycopy" if is_copy(N, tuple(sorted(Y))) else "")


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    run(N)
