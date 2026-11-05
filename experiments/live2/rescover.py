"""rescover.py N1 N2 [noadj]: which 2-sets {u < v} of [N] are shown co-reachable by residue
chains alone (PROOFS.txt 3), recursively:
  {u,v} co-reachable in N  <=  k | v-u, k >= 2, the class s = u mod k can come first in a
  residue chain (RS: always, except k not a power of 2 and (N = 1 mod k, s = 1) or
  (N = -1 mod k, s = k)), and the preimage pair is co-reachable in the class strip.
Base: strips of size <= 3 (everything co-reachable), and adjacent pairs {r, r+1} (assumed
co-reachable, the Adjacent Lemma, unless 'noadj': then only in strips of size <= ADJ_BASE).
Prints the 2-sets not covered (excluding the dead {1,N}, N even >= 4, and {1,7}, N = 7)."""
import sys
from functools import lru_cache

NOADJ = 'noadj' in sys.argv[3:]
NEAR = 'near' in sys.argv[3:]
ADJ_BASE = 24  # adjacent pairs verified co-reachable by computation for N <= 24


def pow2(k):
    return k & (k - 1) == 0


def first_ok(N, k, s):
    if pow2(k):
        return True
    nu = N % k
    if nu == 1 % k and s == 1:
        return False
    if nu == k - 1 and s == k:
        return False
    return True


@lru_cache(maxsize=None)
def cov(N, u, v):
    if u > v:
        u, v = v, u
    if N <= 3:
        return True
    if v - u == 1:
        return (not NOADJ) or N <= ADJ_BASE
    d = v - u
    for k in range(2, d + 1):
        if d % k:
            continue
        s = (u - 1) % k + 1
        n = (N - s) // k + 1
        uu, vv = (u - s) // k + 1, (v - s) // k + 1
        if not first_ok(N, k, s):
            # exceptional class: near residue class (swap an end element), if the pair
            # avoids one of the two end elements of the class
            if not NEAR or (uu == 1 and vv == n):
                continue
        if (uu, vv) == (1, n) and (n % 2 == 0 and n >= 4 or n == 7):
            continue
        if cov(n, uu, vv):
            return True
    mu, mv = N + 1 - v, N + 1 - u
    if (mu, mv) < (u, v):
        return cov(N, mu, mv)
    return False


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    miss = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1)
            if not ((u, v) == (1, N) and (N % 2 == 0 and N >= 4 or N == 7)) and not cov(N, u, v)]
    print(N, len(miss), miss[:30])
