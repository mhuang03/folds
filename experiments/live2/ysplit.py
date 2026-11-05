"""ysplit.py N1 N2: for each Beatty copy X(N,p,g), does Y = [N] \\ X split as Z + W with Z, W
window copies and Z balanced around every w in W (so Z then W is valid from scratch)?"""
import sys
from lib import load_copies, is_copy, arms


def beatty_copies(N):
    seen = set()
    for p in range(2, N):
        for g in range(2 * p - 1 - N, 1):
            X = tuple((r * N + g) // p for r in range(1, p + 1))
            if X not in seen:
                seen.add(X)
                yield p, g, X


def balanced(N, Z, w):
    L, R = arms(N, w)
    return len(L & Z) == len(R & Z)


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    copies = [frozenset(X) for X, _ in load_copies(N)]
    for p, g, X in beatty_copies(N):
        Y = frozenset(range(1, N + 1)) - set(X)
        found = []
        if is_copy(N, Y):
            found.append(('Ycopy',))
        for Z in copies:
            if Z <= Y and Z != Y:
                W = Y - Z
                if len(W) >= 1 and (len(W) == 1 or is_copy(N, W)) and all(balanced(N, Z, w) for w in W):
                    found.append((sorted(Z),))
        print(N, p, g, list(X), 'splits:', len(found), found[:2])
