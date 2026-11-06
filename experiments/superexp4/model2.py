"""Model of the all-N exponent with extra tools:
  doubling splits a((2j+1)n) >= 2 a(jn) a((j+1)n)   (Copies.lean)
  shifted blocks  a(2n) >= a(n-1) a(n+1)            (Extremal.lean, n odd)
  Jensen          B(n) >= 2^{(n-1)/4} a(n)^2        (paper, superexp2 Thm 5)
usage: python3 model2.py [flags]  flags: D (doubling splits) S (shifted) J (Jensen) G=<g> (odd gain)
Reports min over random N of A(N)/(N log2 N) at several scales.
"""
import sys
import random
from functools import lru_cache
from math import log2

sys.setrecursionlimit(1000000)
FL = sys.argv[1] if len(sys.argv) > 1 else ''
G = 0.0
for a in sys.argv[1:]:
    if a.startswith('G='):
        G = float(a[2:])


def small_odd_divs(N, lim=15):
    return [d for d in range(3, lim + 1, 2) if N % d == 0]


@lru_cache(maxsize=None)
def A(N):
    if N <= 1:
        return 0.0
    best = 0.0
    if N % 2:
        n = N // 2
        best = max(1, G * n) + A(n) + A(n + 1)
    else:
        best = max(B(N // 2), 1 + 2 * A(N // 2))
        if 'S' in FL and (N // 2) % 2 == 1 and N >= 4:
            best = max(best, A(N // 2 - 1) + A(N // 2 + 1))
    if 'D' in FL:
        for d in small_odd_divs(N):
            j, n = (d - 1) // 2, N // d
            best = max(best, 1 + A(j * n) + A((j + 1) * n))
    return best


@lru_cache(maxsize=None)
def B(n):
    if n <= 1:
        return 0.0
    best = 2 * A(n)
    if 'J' in FL:
        best = max(best, (n - 1) / 4 + 2 * A(n))
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
    random.seed(1)
    for L in [20, 40, 64]:
        worst = (9, None)
        cands = [2 ** L // 3, 2 ** (L + 1) // 3] + [random.randrange(2 ** (L - 1), 2 ** L) for _ in range(3)]
        for N in cands:
            v = A(N) / (N * log2(N))
            worst = min(worst, (v, N))
        print(L, f"worst {worst[0]:.4f}  at N = {bin(worst[1])}", f" 2^L/3: {A(2**L//3)/(2**L//3*log2(2**L//3)):.4f}")
