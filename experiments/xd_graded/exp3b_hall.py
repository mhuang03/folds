"""Experiment 3b: Hall violators between consecutive ranks of the live graph.

Usage: python3 exp3b_hall.py N [N ...]

For each rank k < N/2 (and the middle step for odd N) computes a maximum matching between
V_k and V_{k+1} (Hopcroft-Karp via scipy) and, when it does not saturate V_k, a minimal
Hall violator: a set X of live k-sets whose live up-neighbourhood N(X) is smaller than X
(X = the vertices of V_k reachable by alternating paths from an unmatched vertex).
Also the maximum antichain of the whole live poset (Dilworth, via a maximum matching in the
comparability graph) for small N: Sperner property.
"""
import sys
import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import maximum_bipartite_matching
from common import vertex_sets, up_edges


def setstr(S, N):
    return "{" + ",".join(str(m) for m in range(1, N + 1) if S >> (m - 1) & 1) + "}"


def hall(N, show=True):
    lev, g, pc = vertex_sets(N, 'live')
    E = up_edges(N, lev, pc)
    sizes = [len(l) for l in lev]
    print(f"N={N} live sizes={sizes}")
    for k in range((N + 1) // 2):
        n, m = sizes[k], sizes[k + 1]
        adj = [[] for _ in range(n)]
        for i, j, _ in E[k]:
            adj[i].append(j)
        B = sp.csr_matrix((np.ones(len(E[k])), ([e[0] for e in E[k]], [e[1] for e in E[k]])),
                          shape=(n, m))
        match = maximum_bipartite_matching(B, perm_type='column')  # for each row, column or -1
        msize = int((match >= 0).sum())
        if msize == min(n, m):
            print(f"  k={k}: |V_k|={n} |V_k+1|={m} matching={msize} (full)")
            continue
        # alternating BFS from one unmatched row
        colmatch = {int(c): i for i, c in enumerate(match) if c >= 0}
        best = None
        for start in [i for i in range(n) if match[i] < 0]:
            X = {start}
            Y = set()
            stack = [start]
            while stack:
                i = stack.pop()
                for j in adj[i]:
                    if j not in Y:
                        Y.add(j)
                        i2 = colmatch[j]
                        if i2 not in X:
                            X.add(i2)
                            stack.append(i2)
            if best is None or len(X) < len(best[0]):
                best = (X, Y)
        X, Y = best
        print(f"  k={k}: |V_k|={n} |V_k+1|={m} matching={msize} deficiency={n - msize};"
              f" smallest alternating violator |X|={len(X)} |N(X)|={len(Y)}")
        if show and len(X) <= 12:
            print("     X    =", " ".join(setstr(lev[k][i], N) for i in sorted(X)))
            print("     N(X) =", " ".join(setstr(lev[k + 1][j], N) for j in sorted(Y)))


def sperner(N):
    lev, g, pc = vertex_sets(N, 'live')
    E = up_edges(N, lev, pc)
    verts = [S for l in lev for S in l]
    idx = {S: i for i, S in enumerate(verts)}
    n = len(verts)
    # reachability: above[i] = bitset of vertices strictly above i
    above = [0] * n
    offs = [0]
    for l in lev:
        offs.append(offs[-1] + len(l))
    for k in range(N - 1, -1, -1):
        for i, j, _ in E[k]:
            a, b = offs[k] + i, offs[k + 1] + j
            above[a] |= above[b] | (1 << b)
    rows, cols = [], []
    for a in range(n):
        x = above[a]
        while x:
            low = x & -x
            rows.append(a)
            cols.append(low.bit_length() - 1)
            x ^= low
    B = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(n, n))
    match = maximum_bipartite_matching(B, perm_type='column')
    width = n - int((match >= 0).sum())
    ncomp = len(rows)
    nincl = sum(1 for a in range(n) for b in range(n)
                if a != b and verts[a] & verts[b] == verts[a]) if n <= 3000 else None
    print(f"N={N}: live poset has {n} elements, {ncomp} comparable pairs (reachability),"
          f" {nincl} strict inclusions; width (max antichain)={width},"
          f" max rank size={max(len(l) for l in lev)}, Sperner={width == max(len(l) for l in lev)}")


if __name__ == '__main__':
    for a in sys.argv[1:]:
        N = int(a)
        hall(N)
        if N <= 13:
            sperner(N)
        sys.stdout.flush()
