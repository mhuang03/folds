"""opt.py N1 N2: for mixed-parity reachable pairs {u,v}, test the two block completions
  A: [u, v] ++ (rest of class(v)) ++ (rest of class(u))
  B: [u, v] ++ (rest of class(u)) ++ (rest of class(v))
(the last block is then automatic by (i) in the class world: complete other class balanced).
Prints the valid orders (u,v) for which neither works (for either valid order of the pair)."""
import sys
from functools import lru_cache


def run(N):
    def ok(S, m):
        r = min(m - 1, N - m)
        return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
            sum(1 for d in range(1, r + 1) if (m + d) in S)

    def fill(start, pool):
        pool = frozenset(pool)

        @lru_cache(None)
        def go(S):
            rest = pool - S
            if not rest:
                return True
            return any(go(S | {m}) for m in rest if ok(S, m))
        return go(frozenset(start))

    bad = []
    for u in range(1, N + 1):
        for v in range(1, N + 1):
            if u == v or (u - v) % 2 == 0 or not ok({u}, v):
                continue
            cv = [x for x in range(1, N + 1) if x % 2 == v % 2 and x != v]
            cu = [x for x in range(1, N + 1) if x % 2 == u % 2 and x != u]
            a = fill({u, v}, cv)
            b = fill({u, v}, cu)
            if not a and not b:
                bad.append((u, v))
    return bad


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    print(N, run(N))
