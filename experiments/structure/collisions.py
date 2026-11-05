"""State compression test: how many distinct values does f(S) (completion count) take,
compared with the number of live sets and live sets up to mirror?  Also: is f(S) determined by
simple statistics of S (|S|, P at a few points, the free-panel imbalance vector)?"""
import sys
from collections import defaultdict
import numpy as np
from common import *

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 14

def mirror(S, N):
    return int(bin(S)[2:].zfill(N)[::-1], 2)

def imbalance(S, N):
    """tuple over free m of (#left - #right) in window; plus the free set itself."""
    out = []
    for m in range(1, N + 1):
        if S >> (m - 1) & 1: continue
        r = min(m - 1, N - m)
        a = sum(S >> (m - d - 1) & 1 for d in range(1, r + 1))
        b = sum(S >> (m + d - 1) & 1 for d in range(1, r + 1))
        out.append(a - b)
    return tuple(out)

for N in range(4, NMAX + 1):
    g = g_array(N); f = f_array(g, N); pc = popcounts(N)
    live = np.nonzero((g > 0) & (f > 0))[0]
    vals = set(int(f[S]) for S in live)
    orb = set(min(int(S), mirror(int(S), N)) for S in live)
    # does the free-panel imbalance pattern (as a sequence, forgetting where the free panels are)
    # together with |S| determine f?
    by_key = defaultdict(set)
    for S in live:
        S = int(S); by_key[(bin(S).count('1'), imbalance(S, N))].add(int(f[S]))
    amb = sum(1 for v in by_key.values() if len(v) > 1)
    print(f"N={N}: live={len(live)} up-to-mirror={len(orb)} distinct f={len(vals)}  "
          f"keys(|S|,imbalance seq)={len(by_key)} ambiguous keys={amb}")
