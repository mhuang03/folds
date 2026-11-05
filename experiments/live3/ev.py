"""ev.py k1 k2: the problem EV(k, w) (PROOFS.txt live3 1.4): a valid ordering of [k] \\ {w} from
scratch in the k-strip (w never placed), starting with 2w, with v before 2v for every v != w
with 2v <= k.  Prints, per k, the w (1 <= w <= k/2) without a solution, and one solution each."""
import sys
from functools import lru_cache


def solve(k, w):
    pts = [v for v in range(1, k + 1) if v != w]
    arm = {}
    for m in pts:
        r = min(m - 1, k - m)
        arm[m] = (range(m - r, m), range(m + 1, m + r + 1))
    target = frozenset(pts)

    @lru_cache(maxsize=None)
    def go(S):
        if S == target:
            return ()
        for m in pts:
            if m in S:
                continue
            if m % 2 == 0 and m // 2 != w and m // 2 not in S:
                continue                       # m/2 must come before m
            L, R = arm[m]
            if sum(1 for x in L if x in S) != sum(1 for x in R if x in S):
                continue
            r = go(S | {m})
            if r is not None:
                return (m,) + r
        return None

    r = go(frozenset({2 * w}))
    return None if r is None else (2 * w,) + r


if __name__ == '__main__':
    for k in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        out = {w: solve(k, w) for w in range(1, k // 2 + 1)}
        print(k, 'fail:', [w for w in out if out[w] is None], {w: out[w] for w in out if out[w]})
