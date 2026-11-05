"""Are valid prefixes low-discrepancy?  For |S| = k ~ N/2, weighted by g(S) (uniform random valid
prefix), compute
  - D(S) = max_j |P(j) - k j / N|      (discrepancy)
  - delta_m = #S in left window - #S in right window, over m not in S (imbalance)
and compare with uniformly random k-sets."""
import sys, math
import numpy as np
from common import *

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
print("N k | valid: E[D] E[delta^2] P(delta=0) | random set: E[D] E[delta^2] P(delta=0)")
for N in range(6, NMAX + 1):
    g = g_array(N).astype(np.float64); pc = popcounts(N)
    k = N // 2
    idx = np.nonzero(pc == k)[0]
    w = g[idx]
    bits = ((idx[:, None] >> np.arange(N)) & 1).astype(np.int64)  # bit j-1 = panel j
    P = np.concatenate([np.zeros((len(idx), 1), np.int64), np.cumsum(bits, 1)], 1)
    j = np.arange(N + 1)
    D = np.abs(P - k * j / N).max(1)
    # imbalance for each m
    d2 = np.zeros(len(idx)); z = np.zeros(len(idx)); cnt = 0
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if r == 0: continue
        left = P[:, m - 1] - P[:, m - 1 - r]
        right = P[:, m + r] - P[:, m]
        free = bits[:, m - 1] == 0
        dd = (left - right)
        d2 += np.where(free, dd ** 2, 0); z += np.where(free, dd == 0, 0); cnt += 1
    nfree = N - k
    def stats(wt):
        wt = wt / wt.sum()
        return (wt @ D, (wt @ d2) / nfree, (wt @ z) / nfree)
    v = stats(w); u = stats(np.ones(len(idx)))
    print(N, k, "| %.3f %.3f %.3f | %.3f %.3f %.3f" % (*v, *u))
