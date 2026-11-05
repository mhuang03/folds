"""chains.py N1 N2: copy chains.  A chain is a partition [N] = X1 + ... + Xk into window copies
such that X1 + ... + X(i-1) is balanced around every element of Xi (then every concatenation of
valid strip orders of the blocks is valid: each block is defect free).  A 2-set {u,v} is
CHAIN-COVERED if u, v lie in the first block X1 of a chain and their preimage pair is live in
the |X1|-strip (or X1 = {u,v}).  Prints the live pairs that are not chain-covered."""
import sys
from functools import lru_cache
from lib import load_copies, arms, live_pair


def run(N):
    copies = [frozenset(X) for X, _ in load_copies(N)]
    if BEATTY:
        bs = set()
        for p in range(2, N):
            for g in range(-N, N):
                X = [(r * N + g) // p for r in range(1, p + 1)]
                if 1 <= X[0] and X[-1] <= N:
                    bs.add(frozenset(X))
                    if MIRROR:
                        bs.add(frozenset(N + 1 - x for x in X))
        copies = [X for X in copies if X in bs]
    if SINGLE:
        copies += [frozenset({m}) for m in range(1, N + 1)]
    full = frozenset(range(1, N + 1))
    armsN = {m: arms(N, m) for m in range(1, N + 1)}

    def bal(U, X):
        for x in X:
            L, R = armsN[x]
            if len(L & U) != len(R & U):
                return False
        return True

    @lru_cache(maxsize=None)
    def completable(U):
        if U == full:
            return True
        for X in copies:
            if not (X & U) and bal(U, X) and completable(U | X):
                return True
        return False

    covered = set()
    for X in copies:
        if len(X) < 2 or not completable(X):
            continue
        xs = sorted(X)
        p = len(xs)
        for i in range(p):
            for j in range(i + 1, p):
                if p == 2 or live_pair(p, i + 1, j + 1):
                    covered.add((xs[i], xs[j]))
    miss = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1)
            if live_pair(N, u, v) and (u, v) not in covered]
    return miss


SINGLE = 'single' in sys.argv[3:]
BEATTY = 'beatty' in sys.argv[3:]
MIRROR = 'mirror' in sys.argv[3:]

if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        m = run(N)
        print(N, len(m), m)
        sys.stdout.flush()
