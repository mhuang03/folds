"""nearord.py q N: an ordering from scratch of the complement of the near residue class
X = C_1 - {1} + {2} (N = 1 mod q) found by DFS (memoised on subsets), printed with the class of
each panel mod q; or 'none'."""
import sys
from functools import lru_cache


def main(q, N, swap=True):
    X = {x for x in range(1, N + 1) if x % q == 1 % q}
    if swap:
        X = (X - {1}) | {2}
    Y = [x for x in range(1, N + 1) if x not in X]
    idx = {x: i for i, x in enumerate(Y)}
    arms = {}
    for m in Y:
        r = min(m - 1, N - m)
        arms[m] = ([idx[x] for x in range(m - r, m) if x in idx],
                   [idx[x] for x in range(m + 1, m + r + 1) if x in idx])
    full = (1 << len(Y)) - 1

    @lru_cache(maxsize=None)
    def go(S):
        if S == full:
            return ()
        for m in Y:
            i = idx[m]
            if S >> i & 1:
                continue
            L, R = arms[m]
            if sum(S >> j & 1 for j in L) == sum(S >> j & 1 for j in R):
                r = go(S | 1 << i)
                if r is not None:
                    return (m,) + r
        return None

    return go(0)


if __name__ == '__main__':
    q, N = int(sys.argv[1]), int(sys.argv[2])
    r = main(q, N, 'noswap' not in sys.argv)
    print(r)
    if r:
        print([x % q if x % q else q for x in r])
