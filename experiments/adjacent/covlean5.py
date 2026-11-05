"""covlean5.py N1 N2: the 2-sets in the Lean family `Cov3` (Folds/Adjacent.lean), computed
faithfully, next to `Cov2` (Folds/Live4.lean, experiments/live4/covlean4.py).

Cov3 = closure of
  cov2     every 2-set of Cov2,
  inward   every set B satisfying the inward criterion (Theorem G of PROOFS.txt): for some
           c2, every panel m outside B has 2m != c2, and
               2m < c2  ->  #(B n L(m)) <= #(B n R(m)),   2m > c2  ->  #(B n L(m)) >= #(B n R(m));
           equivalently: every panel outside B with negative imbalance I_B(m) = #(B n L) -
           #(B n R) lies left of every panel outside B with positive imbalance;
under residue transfers through good classes (the rule `res` of Cov2), through the multiples
of q when q | N + 1 (rule `mult`: the class C_q is a window copy whose complement is reachable
by Theorem G, `coReach_mult`; for q not a power of 2 these are exceptional classes), and the
mirror.
In particular every interval, so every adjacent pair, is in Cov3.

Prints per N: non-dead 2-sets, |Cov2|, |inward pairs|, |Cov3|, then valid prefixes and mixed
parity (Cov2 / Cov3), and with -m the missing pairs.
"""
import os
import sys
from functools import lru_cache

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'live4'))
import covlean4 as C4  # noqa: E402


def inward(N, u, v):
    """The inward criterion for B = {u, v}, u < v."""
    maxneg, minpos = 0, N + 1
    for m in range(1, N + 1):
        if m == u or m == v:
            continue
        r = min(m - 1, N - m)
        lc = (m - r <= u < m) + (m - r <= v < m)
        rc = (m < u <= m + r) + (m < v <= m + r)
        if lc < rc:
            maxneg = m
        elif lc > rc and m < minpos:
            minpos = m
    return maxneg < minpos


def make_cov3(cov2):
    @lru_cache(maxsize=None)
    def cov(N, u, v):
        if u > v:
            u, v = v, u
        if cov2(N, u, v) or inward(N, u, v):
            return True
        for q in range(2, N + 1):
            if (v - u) % q:
                continue
            s = (u - 1) % q + 1
            if (N % q, s) not in C4.good_set(q) and not (s == q and (N + 1) % q == 0):
                continue
            n = (N - s) // q + 1
            if cov(n, (u - s) // q + 1, (v - s) // q + 1):
                return True
        mu, mv = N + 1 - v, N + 1 - u
        if (mu, mv) < (u, v):
            return cov(N, mu, mv)
        return False
    return cov


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    show = '-m' in sys.argv
    cov2 = C4.make_cov(True)
    cov3 = make_cov3(cov2)
    for N in range(int(args[0]), int(args[1]) + 1):
        P = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1) if not C4.dead(N, u, v)]
        c2 = sum(cov2(N, *p) for p in P)
        ci = sum(inward(N, *p) for p in P)
        c3 = sum(cov3(N, *p) for p in P)
        V = [p for p in P if C4.valid(N, *p)]
        M = [p for p in P if (p[1] - p[0]) % 2]
        print(N, len(P), 'Cov2', c2, 'inward', ci, 'Cov3', c3,
              '| valid', len(V), sum(cov2(N, *p) for p in V), sum(cov3(N, *p) for p in V),
              '| mixed', len(M), sum(cov2(N, *p) for p in M), sum(cov3(N, *p) for p in M))
        if show:
            print('   missing:', [p for p in P if not cov3(N, *p)])
