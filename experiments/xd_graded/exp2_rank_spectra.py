"""Experiment 2: ranks of U_k, the Peck/sl2 test, spectra and Smith normal forms.

Usage: python3 exp2_rank_spectra.py NMAX [SPECMAX] [kinds]

For every N <= NMAX and vertex set (all / reach / live):
  rank U_k (exact, over Q)                      -> injective below the middle?
  rank and det of the chain matrix M_k = U^{N-2k} : V_k -> V_{N-k}   (Peck test;
      M_k[S, S'] = number of valid chains from S to complement(S'), a symmetric matrix)
  for |V_k| <= SPECMAX: factored characteristic polynomial of U_k^T U_k (= D U on rank k)
      and the Smith normal form of U_k and of D U.
"""
import sys
from collections import Counter
import flint
from common import vertex_sets, up_edges, A


def mat(rows, cols, entries):
    M = [[0] * cols for _ in range(rows)]
    for (i, j), v in entries.items():
        M[i][j] = v
    return flint.fmpz_mat(M) if rows and cols else None


def fac_str(n):
    n = int(n)
    if n == 0:
        return "0"
    s = "-" if n < 0 else ""
    f = flint.fmpz(abs(n)).factor()
    return s + ("*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in f) or "1")


def main():
    NMAX = int(sys.argv[1])
    SPECMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    kinds = sys.argv[3].split(',') if len(sys.argv) > 3 else ['all', 'reach', 'live']
    for N in range(1, NMAX + 1):
        for kind in kinds:
            lev, g, pc = vertex_sets(N, kind)
            E = up_edges(N, lev, pc)
            sizes = [len(l) for l in lev]
            print(f"N={N} {kind}: sizes={sizes}")
            U = []
            for k in range(N):
                ent = Counter()
                for i, j, _ in E[k]:
                    ent[(j, i)] += 1
                U.append(mat(sizes[k + 1], sizes[k], ent))
            ranks = [U[k].rank() for k in range(N)]
            full = [ranks[k] == min(sizes[k], sizes[k + 1]) for k in range(N)]
            print(f"   rank U_k = {ranks}  full={''.join('Y' if f else 'n' for f in full)}")
            # Peck test
            full_mask = (1 << N) - 1
            for k in range(0, N // 2 + (N % 2)):
                # M = U_{N-k-1} ... U_k
                M = U[k]
                for j in range(k + 1, N - k):
                    M = U[j] * M
                # reindex rows by complement so that M becomes square symmetric
                if kind != 'reach':
                    idx = {S: i for i, S in enumerate(lev[N - k])}
                    perm = [idx[full_mask ^ S] for S in lev[k]]
                    Ms = flint.fmpz_mat([[int(M[perm[i], j]) for j in range(sizes[k])]
                                         for i in range(sizes[k])])
                    sym = all(Ms[i, j] == Ms[j, i] for i in range(sizes[k])
                              for j in range(i))
                    r = Ms.rank()
                    tr = sum(int(Ms[i, i]) for i in range(sizes[k]))
                    line = (f"   chain matrix k={k}: n={sizes[k]} rank={r} sym={sym}"
                            f" trace={tr}")
                    if r == sizes[k] and sizes[k] <= 700:
                        line += f" det={fac_str(Ms.det())}"
                    if sizes[k] <= SPECMAX:
                        cp = Ms.charpoly()
                        c, fs = cp.factor()
                        degs = sorted(Counter((f.degree(), e) for f, e in fs).items())
                        line += f" charpoly factor (deg,mult):count={degs}"
                    print(line)
                else:
                    print(f"   chain matrix k={k}: {M.nrows()}x{M.ncols()} rank={M.rank()}")
            for k in range(N):
                if sizes[k] <= SPECMAX and sizes[k + 1] <= 4 * SPECMAX:
                    DU = U[k].transpose() * U[k]
                    cp = DU.charpoly()
                    c, fs = cp.factor()
                    desc = []
                    for f, e in sorted(fs, key=lambda t: (t[0].degree(), str(t[0]))):
                        if f.degree() == 1:
                            desc.append(f"({-int(f[0])})^{e}")
                        else:
                            desc.append(f"[deg{f.degree()}]^{e}")
                    snf = Counter(int(DU.snf()[i, i]) for i in range(sizes[k]))
                    snfU = Counter(int(U[k].snf()[i, i])
                                   for i in range(min(sizes[k], sizes[k + 1])))
                    print(f"   k={k} DU eig: {' '.join(desc)}")
                    print(f"        SNF(DU)={dict(sorted(snf.items()))}"
                          f" SNF(U)={dict(sorted(snfU.items()))} det(DU)={fac_str(DU.det())}")
            sys.stdout.flush()


if __name__ == '__main__':
    main()
