"""For positions p < q with a_p = a_q (mod 2): the number of outside positions
o = (p-1) + (N-q).  Minimum over all sequences and pairs, and extremal examples."""
import sys
from apfree import enum

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for N in range(3, Nmax + 1):
    L = enum(N)
    best = None
    ex = []
    for w in L:
        for p in range(N):
            for q in range(p + 1, N):
                if (w[p] - w[q]) % 2 == 0:
                    o = p + (N - 1 - q)
                    if best is None or o < best:
                        best = o; ex = []
                    if o == best and len(ex) < 6:
                        ex.append((w, p + 1, q + 1))
    print(f'N={N:2d} min outside = {best}  2*floor((N+1)/4) = {2 * ((N + 1) // 4)}')
    for e in ex:
        print('    ', e)
