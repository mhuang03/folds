"""bchain.py N: for each Beatty copy X(N,p,g), a shortest copy chain completing it
(blocks of size >= 2 that are window copies, each balanced by what precedes)."""
import sys
from functools import lru_cache
from lib import load_copies, arms
from showchains import beatty_tag

N = int(sys.argv[1])
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
    if U == full:
        return ()
    res = None
    for X in copies:
        if not (X & U) and bal(U, X):
            r = best(U | X)
            if r is not None and (res is None or len(r) + 1 < len(res)):
                res = (X,) + r
    return res


seen = set()
for p in range(2, N):
    for g in range(2 * p - 1 - N, 1):
        X = tuple((r * N + g) // p for r in range(1, p + 1))
        if X in seen:
            continue
        seen.add(X)
        r = best(frozenset(X))
        print(p, g, list(X), '->', None if r is None else
              ' | '.join(f'{sorted(B)}{beatty_tag(N, sorted(B))}' for B in r))
