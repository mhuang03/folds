"""gpblocks.py n1 n2: GP(n, B) (PROOFS.txt live3 1.5) with ODD start u0 >= 3, restricted to
block chains mod j of the n-strip (classes {x = a mod j} placed as complete blocks), for each
j.  Prints per n the list of (u0, [j that work])."""
import sys
from functools import lru_cache


def arms(k, m):
    r = min(m - 1, k - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def solve(n, u0, j):
    K = (n + 1) // 2
    A = {m: arms(n, m) for m in range(1, n + 1)}
    cls = {x: x % j for x in range(1, n + 1)}
    blk = {a: frozenset(x for x in range(1, n + 1) if x % j == a) for a in range(j)}

    def ok(S, y):
        L, R = A[y]
        if sum(1 for x in L if x in S) != sum(1 for x in R if x in S):
            return False
        if y == 1:
            return True
        g = 2 * y - 1 if y <= K else None
        return (1 in S) == ((g in S) if g else False)

    @lru_cache(maxsize=None)
    def go(S):
        if len(S) == n:
            return True
        cur = [a for a in range(j) if S & blk[a] and not blk[a] <= S]
        for y in range(1, n + 1):
            if y in S:
                continue
            if cur and cls[y] != cur[0]:
                continue
            if ok(S, y) and go(S | {y}):
                return True
        return False

    return ok(frozenset(), u0) and go(frozenset({u0}))


if __name__ == '__main__':
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        out = []
        for u0 in range(3, n + 1, 2):
            out.append((u0, [j for j in range(2, n) if solve(n, u0, j)]))
        print(n, out, flush=True)
