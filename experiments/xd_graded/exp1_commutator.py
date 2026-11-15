"""Experiment 1: rank sizes, edge counts and the commutator C_k = D_{k+1}U_k - U_{k-1}D_k.

Usage: python3 exp1_commutator.py NMAX [RANKMAX]
D = U^T.  For each N and each vertex set (all / reach / live) prints
  sizes |V_k|, edge counts e_k,
  for every k: number of off-diagonal +1 / -1 entries of C_k, the multiset of diagonal
  entries (as value:count), the rank of C_k (exact over Q via a mod-p rank, sizes <= RANKMAX).
"""
import sys
from collections import Counter
import numpy as np
import scipy.sparse as sp
from common import vertex_sets, up_edges, A

P = 2147483629  # prime < 2^31


def rank_mod_p(M, p=P):
    """Rank of an integer matrix (numpy int64) modulo p, via python-flint."""
    import flint
    r, c = M.shape
    if r == 0 or c == 0:
        return 0
    m = flint.nmod_mat(r, c, [int(x) % p for x in M.reshape(-1)], p)
    return m.rank()


def main():
    NMAX = int(sys.argv[1])
    RANKMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    for N in range(1, NMAX + 1):
        for kind in ('all', 'reach', 'live'):
            lev, g, pc = vertex_sets(N, kind)
            E = up_edges(N, lev, pc)
            sizes = [len(l) for l in lev]
            ecount = [len(e) for e in E]
            print(f"N={N} {kind}: sizes={sizes} total={sum(sizes)}")
            print(f"   edges={ecount}")
            U = []
            for k in range(N):
                if E[k]:
                    i, j, _ = zip(*E[k])
                else:
                    i, j = (), ()
                # U_k as a |V_{k+1}| x |V_k| matrix (maps rank k to rank k+1)
                U.append(sp.csr_matrix((np.ones(len(i), dtype=np.int64), (j, i)),
                                       shape=(sizes[k + 1], sizes[k])))
            # check a(N) = number of maximal chains
            v = np.ones(1, dtype=np.int64)
            for k in range(N):
                v = U[k].dot(v)
            assert int(v[0]) == A[N], (N, kind, v)
            for k in range(0, N + 1):
                n = sizes[k]
                C = sp.csr_matrix((n, n), dtype=np.int64)
                if k < N:
                    C = C + U[k].T.dot(U[k])
                if k > 0:
                    C = C - U[k - 1].dot(U[k - 1].T)
                C = sp.csr_matrix(C)
                C.eliminate_zeros()
                diag = C.diagonal()
                off = C - sp.diags(diag)
                off.eliminate_zeros()
                offc = Counter(off.data.tolist())
                dc = Counter(diag.tolist())
                rk = rank_mod_p(C.toarray()) if n <= RANKMAX else None
                print(f"   k={k:2d} n={n:5d} offdiag +1:{offc.get(1,0)} -1:{offc.get(-1,0)}"
                      f" other:{sum(c for v_, c in offc.items() if v_ not in (1,-1))}"
                      f" diag={dict(sorted(dc.items()))} sum_diag={int(diag.sum())}"
                      f" rank={rk}")
            sys.stdout.flush()


if __name__ == '__main__':
    main()
