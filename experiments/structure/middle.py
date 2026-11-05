"""Which half-way sets S (|S| = floor(N/2)) carry the mass of a(N) = sum g(S) g(S^c)?
Prints the heaviest sets and the effective number exp(entropy) of the weight distribution."""
import sys, math
import numpy as np
from common import *

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 18
for N in range(4, NMAX + 1):
    g = g_array(N).astype(object); pc = popcounts(N); full = (1 << N) - 1
    k = N // 2
    idx = [int(S) for S in np.nonzero(pc == k)[0]]
    w = [(int(g[S]) * int(g[full ^ S]), S) for S in idx]
    tot = sum(x for x, _ in w); assert tot == A[N - 1]
    w = [(x, S) for x, S in w if x]
    H = -sum(x / tot * math.log(x / tot) for x, _ in w)
    w.sort(reverse=True)
    top = " ".join(f"{''.join('x' if S >> j & 1 else '.' for j in range(N))}:{x/tot:.3f}" for x, S in w[:4])
    print(f"N={N} support={len(w)}/{math.comb(N,k)} eff={math.exp(H):.1f}  top: {top}")
