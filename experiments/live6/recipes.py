"""recipes.py N1 N2: for each wide pair (u <= u' = N+1-v), the Beatty witnesses
(orientation R = right-aligned X(N,p,h) or L = its mirror, p, h, preimage a, b) with non-dead
preimage.  Prints statistics of the 'index of u' a (for R: the preimage of the pair's smaller
element is a; for L: of the larger element counted from the right)."""
import sys
from collections import Counter
from ucov import dead, inward


def witnesses(N, u, v):
    out = []
    for p in range(2, (N + 1) // 2 + 1):
        for h in (0, 1):
            if h + 2 * p > N + 1:
                continue
            X = {(r * N - h) // p: r for r in range(1, p + 1)}
            if u in X and v in X and not dead(p, X[u], X[v]):
                out.append(('R', p, h, X[u], X[v]))
            uu, vv = N + 1 - v, N + 1 - u
            if uu in X and vv in X and not dead(p, X[uu], X[vv]):
                out.append(('L', p, h, p + 1 - X[vv], p + 1 - X[uu]))
    return out


if __name__ == '__main__':
    N1, N2 = int(sys.argv[1]), int(sys.argv[2])
    stats = Counter()
    for N in range(N1, N2 + 1):
        for u in range(1, N + 1):
            for v in range(u + 1, N + 1):
                up = N + 1 - v
                if u > up or dead(N, u, v) or inward(N, u, v) or (v - u) % 2 == 0:
                    continue
                w = witnesses(N, u, v)
                kinds = set()
                for t, p, h, a, b in w:
                    if t == 'R' and a == 1:
                        kinds.add('R1')
                    if t == 'L' and a == 1:
                        kinds.add('L1')
                    if t == 'R' and p + 1 - b == 1:
                        kinds.add('Rend')
                    if t == 'L' and p + 1 - b == 1:
                        kinds.add('Lend')
                kinds.add('any' if w else 'none')
                stats[tuple(sorted(kinds))] += 1
    for k, c in sorted(stats.items(), key=lambda x: -x[1]):
        print(c, k)
