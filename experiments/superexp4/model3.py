"""Model: superexp2 system + (U) upper averaging for B(odd n): +U*n bits,
 + (G) odd node gain g*n.  usage: python3 model3.py U g"""
import sys
from functools import lru_cache
from math import log2
sys.setrecursionlimit(1000000)
U = float(sys.argv[1])
G = float(sys.argv[2])


@lru_cache(maxsize=None)
def A(N):
    if N <= 1:
        return 0.0
    if N % 2:
        n = N // 2
        return max(1, G * n) + A(n) + A(n + 1)
    return max(B(N // 2), 1 + 2 * A(N // 2))


@lru_cache(maxsize=None)
def B(n):
    if n <= 1:
        return 0.0
    best = 2 * A(n)
    if n % 2 == 0:
        m = n // 2
        best = max(best, m + 2 * A(m) + B(m))
    else:
        best = max(best, M(n, n, (n - 1) // 2) + U * n)
    return best


@lru_cache(maxsize=None)
def M(x, y, r):
    base = A(x) + A(y)
    if r <= 0:
        return base
    return max(base, (r + 1) // 2 + A((x + 1) // 2) + A(y // 2) + M(x // 2, (y + 1) // 2, r // 2))


for L in [20, 40, 64, 128, 256]:
    N = 2 ** L // 3
    print(L, f"{A(N) / (N * log2(N)):.4f}", f"{A(2*N) / (2*N * log2(2*N)):.4f}")
