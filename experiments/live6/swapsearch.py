"""swapsearch.py N1 N2: for every hard-core pair (core.py) search 'Beatty copies with one
moved element': X = X(N,p,h) or its mirror, containing one of u, v, with one element replaced
by the other one; report those that are inward window copies with a non-dead preimage."""
import sys
from core import core
from ucov import dead
from twoside import is_inward_copy


def search(N, u, v, limit=3):
    out = []
    for p in range(2, (N + 1) // 2 + 1):
        for h in (0, 1):
            if h + 2 * p > N + 1:
                continue
            base = [(r * N - h) // p for r in range(1, p + 1)]
            for orient in ('R', 'L'):
                X = base if orient == 'R' else sorted(N + 1 - x for x in base)
                S = set(X)
                for have, want in ((u, v), (v, u)):
                    if have not in S or want in S:
                        continue
                    for i in range(p):
                        if X[i] == have:
                            continue
                        Y = sorted(X[:i] + X[i + 1:] + [want])
                        a, b = Y.index(u) + 1, Y.index(v) + 1
                        if dead(p, a, b):
                            continue
                        if is_inward_copy(N, Y):
                            out.append((orient, p, h, X[i], (a, b)))
                            if len(out) >= limit:
                                return out
    return out


if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        for (u, v) in core(N, {'beatty', 'dbl', 'one'}):
            print(N, (u, v), search(N, u, v), flush=True)
