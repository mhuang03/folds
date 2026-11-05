"""The Lean-friendly two-function system (log2 values), all N:

  a(2n+1) >= 2 a(n) a(n+1)                         (parity blocks)
  a(2n)   >= B(n),   B(n) = sum_D #condF(n,D) #condS(n,D)   (slip lemma)
  B(2m)   >= 2^m a(m)^2 B(m)                       (chain lemma)
  B(2m+1) >= 2^{floor((m+1)/2)} a(m)^2 a(m+1)^2    (parity slip, odd n)
  B(n)    >= a(n)^2                                (D = empty)

Prints, per dyadic range [2^L, 2^{L+1}), the worst value of (log2 a + K N)/(N log2 N).
"""
import sys
from functools import lru_cache
from math import log2

sys.setrecursionlimit(100000)


@lru_cache(maxsize=None)
def A(N):
    if N <= 1:
        return 0.0
    if N % 2:
        n = N // 2
        return 1 + A(n) + A(n + 1)
    return max(B(N // 2), 1 + 2 * A(N // 2))


@lru_cache(maxsize=None)
def B(n):
    if n <= 1:
        return 0.0
    m = n // 2
    if n % 2 == 0:
        v = m + 2 * A(m) + B(m)
    else:
        v = (m + 1) // 2 + 2 * A(m) + 2 * A(m + 1)
    return max(v, 2 * A(n))


if __name__ == "__main__":
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    for L in range(4, Lmax + 1):
        row = []
        for K in [0, 0.5, 1]:
            v, N = min(((A(N) + K * N) / (N * log2(N)), N) for N in range(2 ** L, 2 ** (L + 1)))
            row.append(f"K={K}: {v:.4f} (N={N})")
        print(L, "pow2:", round(A(2 ** L) / (L * 2 ** L), 4), " | ".join(row))
