"""excreach.py q1 q2 Nmax: is the complement of the EXCEPTIONAL class reachable from scratch?
C_1 for N = 1 (mod q) and C_q for N = -1 (mod q), all q1 <= q <= q2, q <= N <= Nmax.
Memoised DFS (stops at the first ordering found).  Prints failures and timing."""
import sys
import time
from functools import lru_cache

sys.setrecursionlimit(10000)


def reach(N, D):
    Y = [x for x in range(1, N + 1) if x not in D]
    idx = {x: i for i, x in enumerate(Y)}
    arms = []
    for m in Y:
        r = min(m - 1, N - m)
        L = sum(1 << idx[x] for x in range(m - r, m) if x in idx)
        R = sum(1 << idx[x] for x in range(m + 1, m + r + 1) if x in idx)
        arms.append((L, R))
    full = (1 << len(Y)) - 1
    seen = set()

    def go(S):
        if S == full:
            return True
        if S in seen:
            return False
        for i, (L, R) in enumerate(arms):
            if not S >> i & 1 and bin(S & L).count('1') == bin(S & R).count('1'):
                if go(S | 1 << i):
                    return True
        seen.add(S)
        return False

    return go(0)


if __name__ == '__main__':
    q1, q2, Nmax = map(int, sys.argv[1:4])
    for q in range(q1, q2 + 1):
        if q & (q - 1) == 0:
            continue
        for N in range(q, Nmax + 1):
            for s, res in ((1, 1), (q, q - 1)):
                if N % q != res:
                    continue
                D = {x for x in range(1, N + 1) if (x - s) % q == 0}
                t = time.time()
                ok = reach(N, D)
                print(q, N, 'C_%d' % s, ok, '%.1fs' % (time.time() - t), flush=True)
