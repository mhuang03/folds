"""mobius.py: the fold poset and its Moebius function.

  python3 mobius.py [NMAX=11] [semi|sym] [show=0]

The FOLD POSET P_N: subsets of [N], S <= T iff T can be reached from S by valid steps
(each new panel balanced w.r.t. the current set).  It is a partial order, graded by |S|,
self-dual under complement; its maximal chains from 0 to [N] are the valid fold sequences.
Convention (d) weak orders with k blocks = chains 0 < S_1 < ... < S_{k-1} < [N], so
  A^d_N(q) = zeta^q(0,[N])   (zeta polynomial),   A^d_N(-1) = mu(0,[N]).

Prints, for each N: the number of live sets (0 <= S <= [N]), mu(0,[N]), the distribution of
the values mu(0,S) over live S, and sum_S mu(0,S) mu(S,[N]) (= A^d_N(-2)).
With show=1 also lists the live sets with mu(0,S) != 0 (as sorted lists).
"""
import sys
from collections import Counter

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 11
KIND = sys.argv[2] if len(sys.argv) > 2 else 'semi'
SHOW = int(sys.argv[3]) if len(sys.argv) > 3 else 0


def build(N):
    full = (1 << N) - 1
    L, R = [], []
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        L.append(sum(1 << (m - d - 1) for d in range(1, r + 1)))
        R.append(sum(1 << (m + d - 1) for d in range(1, r + 1)))
    bal = [0] * (1 << N)
    for S in range(1 << N):
        b = 0
        for i in range(N):
            if KIND == 'semi':
                ok = bin(S & L[i]).count('1') == bin(S & R[i]).count('1')
            else:
                m = i + 1
                r = min(m - 1, N - m)
                ok = all(((S >> (m - d - 1)) & 1) == ((S >> (m + d - 1)) & 1) for d in range(1, r + 1))
            if ok:
                b |= 1 << i
        bal[S] = b
    return full, bal


def up_sets(N, full, bal, S):
    """list of B (nonzero, disjoint from S) with S <= S|B in the fold poset"""
    comp = full & ~S
    r = {0: True}
    out = []
    B = (-comp) & comp
    while B:
        ok = False
        t = B
        while t:
            i = (t & -t).bit_length() - 1
            t &= t - 1
            B2 = B ^ (1 << i)
            if r.get(B2) and (bal[S | B2] >> i) & 1:
                ok = True
                break
        if ok:
            r[B] = True
            out.append(B)
        B = (B - comp) & comp
    return out


def main():
    for N in range(1, NMAX + 1):
        full, bal = build(N)
        # reachable from 0
        ups0 = up_sets(N, full, bal, 0)
        reach0 = set(ups0) | {0}
        # live: reachable from 0 and reaching full; by complement self-duality S co-reachable
        # iff complement reachable
        live = sorted((S for S in reach0 if (full & ~S) in reach0), key=lambda S: (bin(S).count('1'), S))
        liveset = set(live)
        below = {S: [] for S in live}          # below[T] = live S < T
        for S in live:
            for B in up_sets(N, full, bal, S):
                T = S | B
                if T in liveset:
                    below[T].append(S)
        mu = {}
        for T in live:
            mu[T] = 1 if T == 0 else -sum(mu[S] for S in below[T])
        dist = Counter(mu.values())
        a2 = sum(mu[S] * mu[full & ~S] for S in live)
        print('N=%2d %s  live=%d  mu(0,[N])=%d  A(-2)=%d  #nonzero mu(0,S)=%d  dist=%s' % (
            N, KIND, len(live), mu[full], a2, sum(1 for S in live if mu[S]), dict(sorted(dist.items()))))
        if SHOW:
            for S in live:
                if mu[S]:
                    print('     mu=%3d  %s' % (mu[S], [i + 1 for i in range(N) if S >> i & 1]))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
