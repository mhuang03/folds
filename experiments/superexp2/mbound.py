"""log2 lower bounds from the restricted-chain system (PROOFS.txt section 3), all N:

  a(2n+1)    >= 2 a(n) a(n+1)
  a(2n)      >= B(n)
  B(2m)      >= 2^m a(m)^2 B(m)                                 (full chain, with wrap)
  B(n)       >= M(n, n, floor((n-1)/2))
  M(x,y,r)   >= 2^{ceil(r/2)} a(ceil(x/2)) a(floor(y/2)) M(floor(x/2), ceil(y/2), floor(r/2))
                                                    (2r <= x, 2r+1 <= y; no wrap)
  M(x,y,0)    = a(x) a(y),   B(n) >= a(n)^2.
M(x,y,r) = sum_{D ⊆ [1,r]} #condF(x,D) #condS(y,D).
mode 'simple' drops M (uses the parity slip for odd n instead).
"""
import sys
from functools import lru_cache
from math import log2

sys.setrecursionlimit(1000000)
MODE = 'full'


@lru_cache(maxsize=None)
def A(N):
    if N <= 1:
        return 0.0
    if N % 2:
        return 1 + A(N // 2) + A(N // 2 + 1)
    return max(B(N // 2), 1 + 2 * A(N // 2))


@lru_cache(maxsize=None)
def B(n):
    if n <= 1:
        return 0.0
    best = 2 * A(n)
    if n % 2 == 0:
        m = n // 2
        best = max(best, m + 2 * A(m) + B(m))
    if MODE == 'full':
        best = max(best, M(n, n, (n - 1) // 2))
    else:
        if n % 2:
            m = n // 2
            best = max(best, (m + 1) // 2 + 2 * A(m) + 2 * A(m + 1))
    return best


@lru_cache(maxsize=None)
def M(x, y, r):
    base = A(x) + A(y)
    if r <= 0:
        return base
    assert 2 * r <= x and 2 * r + 1 <= y
    return max(base, (r + 1) // 2 + A((x + 1) // 2) + A(y // 2) + M(x // 2, (y + 1) // 2, r // 2))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == 'simple':
        MODE = 'simple'
    for L in [10, 16, 20, 40, 80, 160, 320, 640]:
        out = []
        for name, N in [("2^L", 2 ** L), ("2^L/3", 2 ** L // 3), ("2^(L+1)/3", 2 ** (L + 1) // 3),
                        ("2^L-1", 2 ** L - 1), ("2^L+1", 2 ** L + 1)]:
            v = A(N)
            out.append(f"{name}: {v / (N * log2(N)):.4f}")
        print(L, "  ".join(out))
