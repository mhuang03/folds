"""Refined statistics: first element, middle position, prefix triangle, reachable sets."""
import sys
import numpy as np
from common import *
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 16
for N in range(1, NMAX + 1):
    g = g_array(N); full = (1 << N) - 1; pc = popcounts(N)
    f = f_array(g, N)
    assert int(g[full]) == A[N-1]
    first = [int(f[1 << (m-1)]) for m in range(1, N+1)]
    T = [int(g[pc == k].sum()) for k in range(N+1)]
    R = [int(((g > 0) & (pc == k)).sum()) for k in range(N+1)]
    live = [int(((g > 0) & (f > 0) & (pc == k)).sum()) for k in range(N+1)]
    print(f"N={N} a={A[N-1]}")
    print("  first:", first)
    print("  T(prefix sums):", T)
    print("  reachable:", R)
    print("  live:", live)
    if N % 2 == 1:
        mid = (N+1)//2; b = 1 << (mid-1)
        pos = [0]*N
        idx = np.nonzero((g > 0) & ((np.arange(1 << N, dtype=np.uint64) & np.uint64(b)) == 0))[0]
        for S in idx:
            S = int(S)
            if step_ok(S, mid, N):
                pos[bin(S).count('1')] += int(g[S]) * int(f[S | b])
        print("  middle pos:", pos)
