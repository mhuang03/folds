"""How general is the 'near' greedy?  Test: single points, all 2-sets (centre = midpoint),
intervals; report failures (sets that are co-reachable per R_N but the greedy gets stuck)."""
import sys
from neargreedy import greedy
from lib import reachable

NMAX = int(sys.argv[1])
f1 = [(N, x) for N in range(2, NMAX + 1) for x in range(1, N + 1)
      if greedy(N, {x}, 2 * x) is None]
print('single points, greedy fails:', f1[:30], len(f1))
f2 = []
for N in range(3, NMAX + 1):
    for u in range(1, N + 1):
        for v in range(u + 1, N + 1):
            if greedy(N, {u, v}, u + v) is None:
                f2.append((N, u, v, reachable(N, set(range(1, N + 1)) - {u, v})))
print('2-sets, greedy fails (N,u,v,coreachable):', [x for x in f2 if x[3]][:40],
      len([x for x in f2 if x[3]]), 'dead:', len([x for x in f2 if not x[3]]))
f3 = []
for N in range(3, NMAX + 1):
    for a in range(1, N + 1):
        for b in range(a + 2, N + 1):
            if greedy(N, set(range(a, b + 1)), a + b) is None:
                f3.append((N, a, b))
print('intervals of length >= 3, greedy fails:', f3[:30], len(f3))
