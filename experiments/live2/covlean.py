"""covlean.py N1 N2: the 2-sets in the Lean family `Cov` (Folds/Live2.lean), computed
faithfully: base N <= 10 (all non-dead 2-sets) or at most one panel left; residue transfer
mod q in 2..8 (q <= N) through non-exceptional classes; mirror.  Prints per N: the number
of non-dead 2-sets, how many are in Cov, how many of the valid (prefix) ones, and the share
of mixed-parity 2-sets covered."""
import sys
from functools import lru_cache

KMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 12
BASE = int(sys.argv[4]) if len(sys.argv) > 4 else 12


def dead(N, u, v):
    return u == 1 and v == N and ((N % 2 == 0 and N >= 4) or N == 7)


def exc(q, nu, s):
    return q & (q - 1) != 0 and ((nu == 1 and s == 1) or (nu + 1 == q and s == q))


@lru_cache(maxsize=None)
def cov(N, u, v):
    if u > v:
        u, v = v, u
    if N <= 3:
        return True
    if N <= BASE:
        return not dead(N, u, v)
    for q in range(2, KMAX + 1):
        if (v - u) % q or q > N:
            continue
        s = (u - 1) % q + 1
        if exc(q, N % q, s):
            continue
        n = (N - s) // q + 1
        if cov(n, (u - s) // q + 1, (v - s) // q + 1):
            return True
    mu, mv = N + 1 - v, N + 1 - u
    if (mu, mv) < (u, v):
        return cov(N, mu, mv)
    return False


def valid(N, u, v):
    return 2 * v >= N + u + 1 or 2 * u <= v


if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        P = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1) if not dead(N, u, v)]
        c = [p for p in P if cov(N, *p)]
        V = [p for p in P if valid(N, *p)]
        cv = [p for p in V if cov(N, *p)]
        M = [p for p in P if (p[1] - p[0]) % 2]
        cm = [p for p in M if cov(N, *p)]
        print(N, len(P), len(c), '| valid', len(V), len(cv), '| mixed', len(M), len(cm))
