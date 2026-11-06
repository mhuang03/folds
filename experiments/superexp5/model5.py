"""Recursion model (log2 counts): superexp4 system (U = upper averaging at B(odd))
 + odd-node slips: a(2n+1) >= 2^{g n} a(e) a(c1) a(c2) (odd child c = c1 + c2 in PB form).
 usage: python3 model5.py U g"""
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
        old = 1 + A(n) + A(n + 1)
        if n >= 2:
            e, c = (n, n + 1) if n % 2 == 0 else (n + 1, n)
            new = G * n + A(e) + A(c // 2) + A(c - c // 2)
            return max(old, new)
        return old
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


if __name__ == "__main__":
    for L in [20, 40, 64, 128, 256, 512]:
        for N in [2 ** L // 3, 2 ** L // 3 + 1, 2 ** L // 3 * 2, 2 ** L - 1, 2 ** L + 1]:
            print(L, N % 8, f"{A(N) / (N * log2(N)):.4f}", end="  ")
        print()
