"""gpshape.py n1 n2: GP(n, B) (PROOFS.txt live3) with ODD start, restricted to the shape
   (odds except 1) ++ (evens > K) ++ [1] ++ (evens <= K),  K = ceil(n/2),
each part in some order.  Prints the odd starts with no solution of that shape."""
import sys
from functools import lru_cache


def arms(k, m):
    r = min(m - 1, k - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def solve(n, u0):
    K = (n + 1) // 2
    phases = [[y for y in range(3, n + 1, 2)],
              [y for y in range(2, n + 1, 2) if y > K],
              [1],
              [y for y in range(2, n + 1, 2) if y <= K]]
    A = {m: arms(n, m) for m in range(1, n + 1)}

    def ok(S, y):
        L, R = A[y]
        if sum(1 for x in L if x in S) != sum(1 for x in R if x in S):
            return False
        if y == 1:
            return True
        one = 1 in S
        g = 2 * y - 1 if y <= K else None
        gp = (g in S) if g else False
        return one == gp

    @lru_cache(maxsize=None)
    def go(S, ph):
        while ph < 4 and all(y in S for y in phases[ph]):
            ph += 1
        if ph == 4:
            return ()
        for y in phases[ph]:
            if y not in S and ok(S, y):
                r = go(S | {y}, ph)
                if r is not None:
                    return (y,) + r
        return None

    if not ok(frozenset(), u0) or u0 not in phases[0]:
        return None
    r = go(frozenset({u0}), 0)
    return None if r is None else (u0,) + r


if __name__ == '__main__':
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        res = {u0: solve(n, u0) for u0 in range(3, n + 1, 2)}
        print(n, 'fail', [u for u in res if res[u] is None], {u: res[u] for u in res if res[u]})
