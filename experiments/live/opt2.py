"""opt2.py N: table over valid mixed orders (u, v): which of the one-level block completions
work.  A = [u,v] ++ class(v) rest ++ class(u) rest,  B = [u,v] ++ class(u) rest ++ class(v)
rest.  Rows u, columns v.  '.' invalid order, 'A', 'B', '*' both, '-' neither, 'x' same
parity."""
import sys
from functools import lru_cache

N = int(sys.argv[1])


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


print("    " + "".join(f"{v:3d}" for v in range(1, N + 1)))
for u in range(1, N + 1):
    row = f"{u:3d} "
    for v in range(1, N + 1):
        if u == v:
            row += "  ."
            continue
        if (u - v) % 2 == 0:
            row += "  x"
            continue
        if not ok({u}, v):
            row += "  ."
            continue
        cv = [x for x in range(1, N + 1) if x % 2 == v % 2 and x != v]
        cu = [x for x in range(1, N + 1) if x % 2 == u % 2 and x != u]
        a = fill({u, v}, cv)
        b = fill({u, v}, cu)
        row += "  " + ("*" if a and b else "A" if a else "B" if b else "-")
    print(row)
