"""smallk.py N1 N2 K B: unconditional coverage.  2-sets shown co-reachable by residue transfers
with moduli k <= K only (RS verified for those k), starting from strips of size <= B where every
2-set except the dead ones is co-reachable (checked by computation).  Prints, per N, the number
of non-dead 2-sets and how many are covered."""
import sys
from functools import lru_cache

N1, N2, K, B = map(int, sys.argv[1:5])


def dead(n, u, v):
    return (u, v) == (1, n) and (n % 2 == 0 and n >= 4 or n == 7)


def first_ok(N, k, s):
    if k & (k - 1) == 0:
        return True
    nu = N % k
    return not ((nu == 1 % k and s == 1) or (nu == k - 1 and s == k))


@lru_cache(maxsize=None)
def cov(N, u, v):
    if u > v:
        u, v = v, u
    if dead(N, u, v):
        return False
    if N <= B:
        return True
    d = v - u
    for k in range(2, min(K, d) + 1):
        if d % k:
            continue
        s = (u - 1) % k + 1
        if not first_ok(N, k, s) or 2 * k > N:
            continue
        n = (N - s) // k + 1
        if cov(n, (u - s) // k + 1, (v - s) // k + 1):
            return True
    mu, mv = N + 1 - v, N + 1 - u
    if (mu, mv) < (u, v):
        return cov(N, mu, mv)
    return False


for N in range(N1, N2 + 1):
    tot = sum(1 for u in range(1, N + 1) for v in range(u + 1, N + 1) if not dead(N, u, v))
    c = sum(1 for u in range(1, N + 1) for v in range(u + 1, N + 1) if cov(N, u, v))
    print(N, tot, c, '%.2f' % (c / tot))
