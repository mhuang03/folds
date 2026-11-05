"""covlean4.py N1 N2 [QMAX]: the 2-sets in the Lean family `Cov2` (Folds/Live4.lean),
computed faithfully, next to the old family `Cov` (Folds/Live2.lean, = covlean.py).

Good classes: the closure `Gd` of Folds/Live4.lean,
  table   q <= 12, every non-exceptional (nu, s)              (good_table)
  zero    nu = 0, every s                                     (good_zero)
  nu_one  q = 2k+1, nu = 1, s = 2v+1 or 2k+2-2v, v odd <= k   (good_nu_one, Theorem H)
  sig     (nu, s) -> (nu, sig(s)),  sig(s) = (nu - s) mod q + 1 (good_sig)
  mirror  (nu, s) -> ((q - nu) mod q, q + 1 - s)              (good_mirror)
  comp    block chains: (j, e, a), (m, inner, y), some (m, c), some (m, c+1) if e > 0
          -> (m j, j c + e, (y - 1) j + a)                     (good_comp)
Cov2: base N <= 12 (non-dead) or at most one panel left; residue transfer mod q (any
2 <= q <= N) through a good class; mirror.

Prints per N: non-dead 2-sets, |Cov|, |Cov2|, then valid prefixes and mixed parity
(Cov / Cov2).  Also prints, with -g, the number of good (nu, s) per q.
"""
import sys
from functools import lru_cache

QMAX = 200


def exc(q, nu, s):
    return q & (q - 1) != 0 and ((nu == 1 and s == 1) or (nu + 1 == q and s == q))


def sig(q, nu, t):
    return (nu - t) % q + 1


def inner(m, c, e, a):
    return (c + 1) % m if a <= e else c


G = {}


def good_set(q):
    if q in G:
        return G[q]
    S = set()
    for t in range(1, q + 1):
        S.add((0, t))
    if 2 <= q <= 12:
        for nu in range(q):
            for s in range(1, q + 1):
                if not exc(q, nu, s):
                    S.add((nu, s))
    if q % 2 == 1 and q >= 3:
        k = (q - 1) // 2
        for v in range(1, k + 1, 2):
            S.add((1, 2 * v + 1))
            S.add((1, 2 * k + 2 - 2 * v))
    for j in range(2, q):
        if q % j:
            continue
        m = q // j
        if m < 2:
            continue
        Gj, Gm = good_set(j), good_set(m)
        hasm = {nu for (nu, _) in Gm}
        for (e, a) in Gj:
            for c in range(m):
                if c not in hasm:
                    continue
                if e > 0 and (c + 1) % m not in hasm:
                    continue
                ci = inner(m, c, e, a)
                for (nu2, y) in Gm:
                    if nu2 == ci:
                        S.add((j * c + e, (y - 1) * j + a))
    while True:
        new = set()
        for (nu, t) in S:
            new.add((nu, sig(q, nu, t)))
            new.add(((q - nu) % q, q + 1 - t))
        if new <= S:
            break
        S |= new
    G[q] = S
    return S


def dead(N, u, v):
    return u == 1 and v == N and ((N % 2 == 0 and N >= 4) or N == 7)


def make_cov(new):
    @lru_cache(maxsize=None)
    def cov(N, u, v):
        if u > v:
            u, v = v, u
        if N <= 3:
            return True
        if N <= 12:
            return not dead(N, u, v)
        for q in range(2, (N if new else 12) + 1):
            if (v - u) % q or q > N:
                continue
            s = (u - 1) % q + 1
            if new:
                if (N % q, s) not in good_set(q):
                    continue
            elif exc(q, N % q, s):
                continue
            n = (N - s) // q + 1
            if cov(n, (u - s) // q + 1, (v - s) // q + 1):
                return True
        mu, mv = N + 1 - v, N + 1 - u
        if (mu, mv) < (u, v):
            return cov(N, mu, mv)
        return False
    return cov


def valid(N, u, v):
    return 2 * v >= N + u + 1 or 2 * u <= v


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    if sys.argv[1] == '-g':
        for q in range(2, int(sys.argv[2]) + 1):
            S = good_set(q)
            print(q, len(S), 'of', q * q, ' nus with some good class:',
                  len({nu for nu, _ in S}))
        sys.exit()
    old, new = make_cov(False), make_cov(True)
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        P = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1) if not dead(N, u, v)]
        c1 = sum(old(N, *p) for p in P)
        c2 = sum(new(N, *p) for p in P)
        V = [p for p in P if valid(N, *p)]
        M = [p for p in P if (p[1] - p[0]) % 2]
        print(N, len(P), 'Cov', c1, 'Cov2', c2,
              '| valid', len(V), sum(old(N, *p) for p in V), sum(new(N, *p) for p in V),
              '| mixed', len(M), sum(old(N, *p) for p in M), sum(new(N, *p) for p in M))
