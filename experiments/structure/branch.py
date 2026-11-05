"""Per-step acceptance rate q(N,k) = T(N,k) / (T(N,k-1) (N-k+1)), where T(N,k) = number of
valid prefixes of length k.  a(N)/N! = prod_k q(N,k).  Also: the same rate restricted to live
prefixes (those that can be completed), i.e. along uniformly random *complete* sequences."""
import sys, math
import numpy as np
from common import *

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
print("N  geo-mean q   q at k/N in (0.25,0.75)  live-geo-mean")
rows = []
for N in range(4, NMAX + 1):
    g = g_array(N); pc = popcounts(N); f = f_array(g, N)
    T = [float(g[pc == k].sum()) for k in range(N + 1)]
    q = [T[k] / (T[k - 1] * (N - k + 1)) for k in range(1, N + 1)]
    # along complete sequences: mean over a random complete sequence of #valid live moves...
    # W(k) = sum_{|S|=k} g f = a(N) for all k; live branching = sum_{|S|=k-1} g(S)*#{m: live successor}/a
    gm = math.exp(sum(math.log(x) for x in q) / N)
    mid = [q[k - 1] for k in range(1, N + 1) if 0.25 < k / N < 0.75]
    rows.append((N, gm, sum(mid) / len(mid)))
    print(N, round(gm, 4), round(sum(mid) / len(mid), 4), " ".join(f"{x:.3f}" for x in q))
print("\nscaling of mid-range q:  q*sqrt(N), q*log(N)")
for N, gm, m in rows:
    print(N, round(m * math.sqrt(N), 3), round(m * math.log(N), 3))
