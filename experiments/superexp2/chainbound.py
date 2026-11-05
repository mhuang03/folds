"""Numerical value of the chain-slip lower bounds (log2), for all N.

Recursions (see PROOFS.txt):
  a(2n)   >= 2^{|C|} * #{tau : G(tau) ⊇ C} * #{sigma : G'(sigma) ⊇ C}   (slip lemma, D = C)
  a(2n+1) >= 2 a(n) a(n+1)
  chain sets (odds-first parity blocks PB(alpha, beta)):
    n = 2m:   G  ⊇ odds ∪ 2 G_m(beta),        G' ⊇ odds ∪ 2 G'_m(alpha)
    n = 2m+1: G  ⊇ {odd k <= m} ∪ {2i : 4i <= n, i in G_m(beta)}
              G' ⊇ {odd k : 2k+1 <= n} ∪ {2i : 4i+1 <= n, i in G'_{m+1}(alpha)}
  Fg(n) = log2 #{tau : G ⊇ Gam(n)} >= A(free half) + Fg(constrained half).
Sets are Python ints used as bitsets (bit k <-> position k).
"""
import sys
from functools import lru_cache
from math import log2

sys.setrecursionlimit(10000)


def odds_upto(lim):
    """bitset of odd k with 1 <= k <= lim"""
    s = 0
    for k in range(1, lim + 1, 2):
        s |= 1 << k
    return s


def double_bits(s, lim):
    """{2i : i in s, 2i <= lim}"""
    r = 0
    i = 0
    while s >> i:
        if (s >> i) & 1 and 2 * i <= lim:
            r |= 1 << (2 * i)
        i += 1
    return r


@lru_cache(maxsize=None)
def gam(n):
    """(bitset Gamma(n), log2 count of tau with G(tau) ⊇ Gamma(n))"""
    if n <= 1:
        return 0, 0.0
    m = n // 2
    if n % 2 == 0:
        sb, fb = gam(m)
        return odds_upto(n - 1) | double_bits(sb, n - 1), A(m) + fb
    # n = 2m+1: beta in V_m constrained on i with 4i <= n
    sb, fb = gam(m)
    keep = 0
    for i in range(1, m):
        if (sb >> i) & 1 and 4 * i <= n:
            keep |= 1 << i
    return odds_upto(m) | double_bits(keep, n - 1), A(m + 1) + fb


@lru_cache(maxsize=None)
def gamp(n):
    """(bitset Gamma'(n), log2 count of sigma with G'(sigma) ⊇ Gamma'(n))"""
    if n <= 1:
        return 0, 0.0
    m = n // 2
    if n % 2 == 0:
        sa, fa = gamp(m)
        return odds_upto(n - 1) | double_bits(sa, n - 1), A(m) + fa
    sa, fa = gamp(m + 1)
    keep = 0
    for i in range(1, m + 1):
        if (sa >> i) & 1 and 4 * i + 1 <= n:
            keep |= 1 << i
    oddk = 0
    for k in range(1, n, 2):
        if 2 * k + 1 <= n:
            oddk |= 1 << k
    return oddk | double_bits(keep, n - 1), A(m) + fa


@lru_cache(maxsize=None)
def A(N):
    if N <= 2:
        return log2([1, 1, 2][N])
    if N % 2 == 1:
        n = N // 2
        return 1 + A(n) + A(n + 1)
    n = N // 2
    s1, f1 = gam(n)
    s2, f2 = gamp(n)
    chain = bin(s1 & s2).count("1") + f1 + f2
    return max(chain, 1 + 2 * A(n))


if __name__ == "__main__":
    Ns = [int(x) for x in sys.argv[1:]] or [2 ** j for j in range(4, 21)]
    for N in Ns:
        v = A(N)
        print(N, round(v, 1), "exponent", round(v / (N * log2(N)), 4),
              "with -N/2 slack:", round((v + N / 2) / (N * log2(N)), 4))
