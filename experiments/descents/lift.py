"""Pair lifts of run labelings.  A labeling rho: [1..n] -> {1..k} defines the order by (rho, m);
it is 'valid' if that order is a valid fold sequence.  Lift to N in {2n+1, 2n+2, 2n+3}:
   rho(2y) = rho'(y) + s0, rho(2y+1) = rho'(y) + s1   (1 <= y <= n),
   boundary panels (1, and 2n+2, 2n+3 when present) get labels chosen from {1..k+1}.
For each N, count lifted labelings that are valid with k+1 = lg(N+1) labels."""
from common import *
from construct_bits import valid_fast
import sys, itertools
def order(rho, N): return sorted(range(1, N + 1), key=lambda m: (rho[m], m))
def labelings(n, k):
    for t in itertools.product(range(1, k + 1), repeat=n):
        rho = dict(zip(range(1, n + 1), t))
        if valid_fast(n, order(rho, n)): yield rho
for n in range(1, int(sys.argv[1]) + 1):
    k = lg(n + 1)
    L = list(labelings(n, k))
    for N in (2*n + 1, 2*n + 2, 2*n + 3):
        K = lg(N + 1)
        if K != k + 1: continue
        res = {}
        for s0, s1 in ((1, 0), (0, 1)):
            for rho0 in L:
                base = {}
                for y in range(1, n + 1):
                    base[2*y] = rho0[y] + s0; base[2*y + 1] = rho0[y] + s1
                extra = [1] + [m for m in range(2*n + 2, N + 1)]
                for labs in itertools.product(range(1, K + 1), repeat=len(extra)):
                    rho = dict(base); rho.update(zip(extra, labs))
                    if max(rho.values()) > K or min(rho.values()) < 1: continue
                    if valid_fast(N, order(rho, N)):
                        key = (s0, s1, labs)
                        res[key] = res.get(key, 0) + 1
        print(f'n={n} (k={k}, {len(L)} labelings) -> N={N}:', res if res else 'NONE', flush=True)
