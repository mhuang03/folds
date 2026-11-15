"""Experiment 3: generic-weight tests on the live graph (and the reachable / full graph).

Usage: python3 exp3_peck.py NMAX [kinds]

Random edge weights modulo a 31-bit prime.  By the Schwartz-Zippel lemma the ranks below
are, with overwhelming probability, the generic ranks (two independent trials are compared):
  gen rank U_k     = size of a maximum matching between V_k and V_{k+1}
  gen rank of U^{N-2k} : V_k -> V_{N-k}
                   = maximum number of vertex-disjoint valid chains from V_k to V_{N-k}
                     (Lindstrom-Gessel-Viennot / Menger); equal to |V_k| for all k < N/2
                     iff the graded graph is Peck in the sense of Proctor-Stanley, iff some
                     weighting of the edges makes U the raising operator of an sl_2
                     representation (Proctor 1982), iff a 'dual' lowering operator D' with
                     D'U - UD' = (N-2k) I exists for that weighting.
"""
import sys
import random
import flint
from common import vertex_sets, up_edges

P = 2147483629


def main():
    NMAX = int(sys.argv[1])
    kinds = sys.argv[2].split(',') if len(sys.argv) > 2 else ['live', 'reach', 'all']
    for N in range(1, NMAX + 1):
        for kind in kinds:
            lev, g, pc = vertex_sets(N, kind)
            E = up_edges(N, lev, pc)
            sizes = [len(l) for l in lev]
            res = []
            for trial in range(2):
                rng = random.Random(1000 * N + trial)
                U = []
                for k in range(N):
                    M = [[0] * sizes[k] for _ in range(sizes[k + 1])]
                    for i, j, _ in E[k]:
                        M[j][i] = rng.randrange(1, P)
                    U.append(flint.nmod_mat(M, P))
                ranks = [U[k].rank() for k in range(N)]
                chain = []
                for k in range(0, (N + 1) // 2):
                    M = U[k]
                    for j in range(k + 1, N - k):
                        M = U[j] * M
                    chain.append(M.rank())
                res.append((ranks, chain))
            assert res[0] == res[1], "trials disagree"
            ranks, chain = res[0]
            matchfull = all(ranks[k] == min(sizes[k], sizes[k + 1]) for k in range(N))
            peck = all(chain[k] == sizes[k] for k in range(len(chain)))
            unimodal = all(sizes[k] <= sizes[k + 1] for k in range(N // 2))
            print(f"N={N} {kind}: sizes={sizes}")
            print(f"   generic rank U_k      = {ranks}  full matchings: {matchfull}")
            print(f"   generic rank U^(N-2k) = {chain}  Peck: {peck}  unimodal: {unimodal}")
            sys.stdout.flush()


if __name__ == '__main__':
    main()
