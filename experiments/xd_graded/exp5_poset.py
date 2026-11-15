"""Experiment 5: the poset L_N of live sets ordered by reachability.

Usage: python3 exp5_poset.py NMAX [FLAGMAX] [LATMAX]

S <= T iff there is a valid chain S -> ... -> T.  L_N is graded by |S| with minimum the
empty set and maximum [N]; the number of maximal chains is a(N).

Prints for each N:
  number of elements, covers, comparable pairs, strict inclusions among live sets
  mu(0, [N]) and the characteristic polynomial chi(t) = sum_S mu(0, S) t^(N-|S|)
  the multiset of Moebius values of intervals of length 2 (thin <=> all equal to 1),
  Eulerian test (mu(S,T) = (-1)^(|T|-|S|) for all S <= T)
  lattice test (N <= LATMAX)
  flag f- and h-vectors (N <= FLAGMAX): min of beta_J, number of negative beta_J,
     beta_[N-1] = |mu(0,1)|, and the zeta polynomial values Z(2) = #elements, Z(3) = #pairs.
"""
import sys
from collections import Counter
from itertools import combinations
import numpy as np
from common import vertex_sets, up_edges, A


def build(N):
    lev, g, pc = vertex_sets(N, 'live')
    E = up_edges(N, lev, pc)
    sizes = [len(l) for l in lev]
    # C[k][l] : boolean matrix |V_k| x |V_l|, comparability (k < l)
    cover = []
    for k in range(N):
        M = np.zeros((sizes[k], sizes[k + 1]), dtype=np.int64)
        for i, j, _ in E[k]:
            M[i, j] = 1
        cover.append(M)
    comp = {}
    for k in range(N):
        cur = cover[k]
        comp[(k, k + 1)] = cur
        for l in range(k + 2, N + 1):
            cur = ((cur @ cover[l - 1]) > 0).astype(np.int64)
            comp[(k, l)] = cur
    return lev, sizes, cover, comp


def moebius_from(N, sizes, comp, k0, i0):
    """mu(x, y) for x = (k0, i0) and all y >= x; returns dict level -> vector."""
    mu = {k0: np.zeros(sizes[k0], dtype=np.int64)}
    mu[k0][i0] = 1
    for l in range(k0 + 1, N + 1):
        tot = np.zeros(sizes[l], dtype=np.int64)
        for k in range(k0, l):
            tot += mu[k] @ comp[(k, l)]
        # only elements above x get a value
        above = comp[(k0, l)][i0]
        mu[l] = -tot * above
    return mu


def main():
    NMAX = int(sys.argv[1])
    FLAGMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    LATMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 9
    for N in range(1, NMAX + 1):
        lev, sizes, cover, comp = build(N)
        n = sum(sizes)
        ncov = sum(int(c.sum()) for c in cover)
        ncomp = sum(int(c.sum()) for c in comp.values())
        nincl = 0
        if N <= 12:
            allv = [S for l in lev for S in l]
            nincl = sum(1 for a in allv for b in allv if a != b and a & b == a)
        mu0 = moebius_from(N, sizes, comp, 0, 0)
        chi = [int(mu0[k].sum()) for k in range(N + 1)]
        print(f"N={N}: elements={n} covers={ncov} comparable={ncomp} inclusions={nincl}")
        print(f"   mu(0,1)={int(mu0[N][0])}  chi coefficients (t^N ... t^0) = {chi}"
              f"  chi(1)={sum(chi)}")
        absmu = [int(np.abs(mu0[k]).sum()) for k in range(N + 1)]
        print(f"   sum_S |mu(0,S)| by rank = {absmu}")
        # intervals of length 2
        c2 = Counter()
        for k in range(N - 1):
            paths = cover[k] @ cover[k + 1]
            vals, cnts = np.unique(paths[paths > 0], return_counts=True)
            for v, c in zip(vals.tolist(), cnts.tolist()):
                c2[v - 1] += c
        print(f"   length-2 intervals by Moebius value (#atoms - 1): {dict(sorted(c2.items()))}")
        if N <= 11:
            eul = True
            bad = 0
            tot = 0
            for k0 in range(N + 1):
                for i0 in range(sizes[k0]):
                    mu = moebius_from(N, sizes, comp, k0, i0)
                    for l in range(k0 + 1, N + 1):
                        above = comp[(k0, l)][i0]
                        want = (-1) ** (l - k0)
                        tot += int(above.sum())
                        bad += int(((mu[l] != want) & (above > 0)).sum())
            print(f"   Eulerian: {bad == 0}  (intervals with mu != (-1)^length: {bad} of {tot})")
        if N <= LATMAX:
            # lattice test via down-sets as bitsets
            allv = [(k, i) for k in range(N + 1) for i in range(sizes[k])]
            off = [0]
            for s in sizes:
                off.append(off[-1] + s)
            below = {}
            for (k, i) in allv:
                b = 1 << (off[k] + i)
                for kk in range(k):
                    col = comp[(kk, k)][:, i]
                    for ii in np.nonzero(col)[0]:
                        b |= 1 << (off[kk] + int(ii))
                below[(k, i)] = b
            downsets = set(below.values())
            nomeet = 0
            for x, y in combinations(allv, 2):
                c = below[x] & below[y]
                if c not in downsets:
                    nomeet += 1
            print(f"   lattice: {nomeet == 0}  (pairs without a meet: {nomeet} of"
                  f" {len(allv) * (len(allv) - 1) // 2})")
        if N <= FLAGMAX and N >= 2:
            ranks = list(range(1, N))
            alpha = {}
            # cnt[J] = vector on V_{max J} counting chains with rank set J ending there
            cnt = {(): None}
            for J_size in range(0, N):
                for J in combinations(ranks, J_size):
                    if J_size == 0:
                        alpha[J] = 1
                        continue
                    prev = J[:-1]
                    r = J[-1]
                    if not prev:
                        vec = np.ones(sizes[r], dtype=object)
                    else:
                        vec = cnt[prev] @ comp[(prev[-1], r)].astype(object)
                    cnt[J] = vec
                    alpha[J] = int(vec.sum())
            assert alpha[tuple(ranks)] == A[N]
            beta = {}
            for J in alpha:
                s = 0
                for sz in range(len(J) + 1):
                    for I in combinations(J, sz):
                        s += (-1) ** (len(J) - sz) * alpha[I]
                beta[J] = s
            neg = [(J, b) for J, b in beta.items() if b < 0]
            print(f"   flag h-vector: min beta={min(beta.values())} negative entries={len(neg)}"
                  f" of {len(beta)}; beta_[N-1]={beta[tuple(ranks)]}"
                  f" (= (-1)^N mu(0,1): {beta[tuple(ranks)] == (-1) ** N * int(mu0[N][0])})")
            if neg:
                neg.sort(key=lambda t: (len(t[0]), t[0]))
                print(f"      first negative: beta_{list(neg[0][0])} = {neg[0][1]}")
            symm = all(beta[J] == beta[tuple(sorted(N - r for r in J))] for J in beta)
            comp_sym = all(beta[J] == beta[tuple(r for r in ranks if r not in J)] for J in beta)
            print(f"      beta_J = beta_(N-J): {symm};  beta_J = beta_(complement J): {comp_sym}")
            print(f"      alpha by |J|: " + ", ".join(
                f"{sz}:{sum(a for J, a in alpha.items() if len(J) == sz)}" for sz in range(N)))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
