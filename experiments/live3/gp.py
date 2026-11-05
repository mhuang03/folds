"""gp.py: brute force for the constrained strip problems of PROOFS.txt (live3), section 1.

GP(n, g): sequences of [1, n], valid in the n-strip, such that when y != 1 is placed,
  [1 already placed] == [g(y) already placed], g(y) in [1, n] or 'T' (always placed) or 'B'
  (never placed).
Usage: python3 gp.py n mode     prints the starts that admit a solution and one solution each.
  mode B: g(y) = 2y-1 for y <= ceil(n/2), 'B' above;  A: 'T' above;  D: 2y-1-n above."""
import sys
from functools import lru_cache


def arms(k, m):
    r = min(m - 1, k - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def make_g(n, mode):
    K = (n + 1) // 2
    g = {}
    for y in range(2, n + 1):
        if y <= K:
            g[y] = 2 * y - 1
        else:
            g[y] = {'B': 'B', 'A': 'T', 'D': 2 * y - 1 - n}[mode]
    return g


def solve(n, g):
    A = {m: arms(n, m) for m in range(1, n + 1)}
    full = (1 << n) - 1

    def okstep(S, y):
        L, R = A[y]
        if sum(S >> (x - 1) & 1 for x in L) != sum(S >> (x - 1) & 1 for x in R):
            return False
        if y == 1:
            return True
        one = S & 1
        gy = g[y]
        gp = 1 if gy == 'T' else 0 if gy == 'B' else (S >> (gy - 1)) & 1
        return one == gp

    @lru_cache(maxsize=None)
    def done(S):
        if S == full:
            return ()
        for y in range(1, n + 1):
            if not S >> (y - 1) & 1 and okstep(S, y):
                r = done(S | 1 << (y - 1))
                if r is not None:
                    return (y,) + r
        return None

    out = {}
    for t in range(1, n + 1):
        if okstep(0, t):
            r = done(1 << (t - 1))
            if r is not None:
                out[t] = (t,) + r
    return out


if __name__ == '__main__':
    n = int(sys.argv[1])
    mode = sys.argv[2]
    res = solve(n, make_g(n, mode))
    for t in range(1, n + 1):
        print(t, res.get(t))
