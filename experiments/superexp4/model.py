"""Model: how much would a free gain of g*n bits at odd nodes N = 2n+1 raise the all-N exponent
of the superexp2 system (mbound.py)?   usage: python3 model.py g
"""
import sys
from functools import lru_cache
from math import log2

sys.setrecursionlimit(1000000)
G = float(sys.argv[1]) if len(sys.argv) > 1 else 0.0


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
    best = max(best, M(n, n, (n - 1) // 2))
    return best


@lru_cache(maxsize=None)
def M(x, y, r):
    base = A(x) + A(y)
    if r <= 0:
        return base
    return max(base, (r + 1) // 2 + A((x + 1) // 2) + A(y // 2) + M(x // 2, (y + 1) // 2, r // 2))


if __name__ == "__main__":
    for L in [20, 80, 320, 640]:
        out = []
        for name, N in [("2^L", 2 ** L), ("2^L/3", 2 ** L // 3), ("2^(L+1)/3", 2 ** (L + 1) // 3)]:
            out.append(f"{name}: {A(N) / (N * log2(N)):.4f}")
        print(L, "  ".join(out))
