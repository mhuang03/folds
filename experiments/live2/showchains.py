"""showchains.py N [k]: for each live 2-set, a shortest copy chain (blocks of size >= 2, see
chains.py) whose first block contains the pair with a live preimage pair.  Blocks are tagged
B(p,g) when they are Beatty sets X(N,p,g)."""
import sys
from functools import lru_cache
from lib import load_copies, arms, live_pair


def beatty_tag(N, X):
    p = len(X)
    for g in range(-N, 1):
        if tuple((r * N + g) // p for r in range(1, p + 1)) == tuple(X):
            return f'B({p},{g})'
    return ''


def run(N, show=True):
    copies = [frozenset(X) for X, _ in load_copies(N)]
    full = frozenset(range(1, N + 1))
    armsN = {m: arms(N, m) for m in range(1, N + 1)}

    def bal(U, X):
        for x in X:
            L, R = armsN[x]
            if len(L & U) != len(R & U):
                return False
        return True

    @lru_cache(maxsize=None)
    def best(U):
        """shortest completion of U by blocks, as a tuple of blocks, or None."""
        if U == full:
            return ()
        res = None
        for X in copies:
            if not (X & U) and bal(U, X):
                r = best(U | X)
                if r is not None and (res is None or len(r) + 1 < len(res)):
                    res = (X,) + r
        return res

    out = {}
    for X in copies:
        r = best(X)
        if r is None:
            continue
        xs = sorted(X)
        p = len(xs)
        for i in range(p):
            for j in range(i + 1, p):
                if p == 2 or live_pair(p, i + 1, j + 1):
                    ch = (X,) + r
                    key = (xs[i], xs[j])
                    if key not in out or len(ch) < len(out[key]):
                        out[key] = ch
    for key in sorted(out):
        ch = out[key]
        if show:
            print(key, ' | '.join(f'{sorted(B)}{beatty_tag(N, sorted(B))}' for B in ch))
    return out


if __name__ == '__main__':
    run(int(sys.argv[1]))
