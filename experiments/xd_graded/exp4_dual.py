"""Experiment 4: linear feasibility of a dual lowering operator D'.

Usage: python3 exp4_dual.py NMAX support[,support...] [kinds]
   support in {gen, bool, edge}

Unknowns: matrices D'_k : V_k -> V_{k-1} (1 <= k <= N) with the given support, and scalars
r_0..r_N.  Equations:  D'_{k+1} U_k - U_{k-1} D'_k = r_k I   on V_k,  for 0 <= k <= N,
where U is the (unweighted) up operator of Gamma_N restricted to the vertex set.

  gen : D' arbitrary
  bool: D'(T, S) may be nonzero only if T = S minus one element (Boolean covers)
  edge: D'(T, S) may be nonzero only if T -> S is an edge of Gamma_N (weighted U^T)

The system is homogeneous in (D', r).  We report (all ranks modulo a 31-bit prime):
  nullity       = dimension of the solution space
  nullity_r0    = dimension of the solutions with r = 0
  dim r-space   = nullity - nullity_r0 = dimension of the set of achievable r
  a basis of the r-space (reduced row echelon form, rational reconstruction).
A relation of differential type exists iff dim r-space > 0.
"""
import sys
from fractions import Fraction
import flint
from common import vertex_sets, up_edges

P = 2147483629


def ratrec(a, p=P):
    """Rational reconstruction of a mod p with small numerator/denominator."""
    a %= p
    r0, r1 = p, a
    s0, s1 = 0, 1
    bound = int((p // 2) ** 0.5)
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return Fraction(r1, s1)


def solve(N, kind, support):
    lev, g, pc = vertex_sets(N, kind)
    E = up_edges(N, lev, pc)
    sizes = [len(l) for l in lev]
    up = [dict() for _ in range(N + 1)]    # up[k][i] = list of j in V_{k+1}
    down = [dict() for _ in range(N + 1)]  # down[k][j] = list of i in V_{k-1}
    for k in range(N):
        for i, j, _ in E[k]:
            up[k].setdefault(i, []).append(j)
            down[k + 1].setdefault(j, []).append(i)
    # unknown index: D'_k(t, s), t in V_{k-1}, s in V_k
    var = {}
    for k in range(1, N + 1):
        for s, S in enumerate(lev[k]):
            for t, T in enumerate(lev[k - 1]):
                if support == 'gen':
                    ok = True
                elif support == 'bool':
                    ok = (T & S) == T
                else:
                    ok = t in down[k].get(s, ())
                if ok:
                    var[(k, t, s)] = len(var)
    nD = len(var)
    nvar = nD + N + 1
    rows = []
    for k in range(N + 1):
        for a in range(sizes[k]):        # row index (in V_k)
            for b in range(sizes[k]):    # column index (in V_k)
                row = {}
                # (D'_{k+1} U_k)(a, b) = sum_{c in V_{k+1}, b -> c} D'_{k+1}(a, c)
                for c in up[k].get(b, ()):
                    v = var.get((k + 1, a, c))
                    if v is not None:
                        row[v] = row.get(v, 0) + 1
                # (U_{k-1} D'_k)(a, b) = sum_{t in V_{k-1}, t -> a} D'_k(t, b)
                for t in down[k].get(a, ()):
                    v = var.get((k, t, b))
                    if v is not None:
                        row[v] = row.get(v, 0) - 1
                if a == b:
                    row[nD + k] = -1
                if row:
                    rows.append(row)
    return sizes, nD, nvar, rows


def analyse(N, kind, support):
    sizes, nD, nvar, rows = solve(N, kind, support)
    M = flint.nmod_mat(len(rows), nvar, P)
    for i, row in enumerate(rows):
        for j, v in row.items():
            M[i, j] = v % P
    X, nullity = M.nullspace()
    # r-part of the null space
    R = flint.nmod_mat(nullity, N + 1, P)
    for c in range(nullity):
        for k in range(N + 1):
            R[c, k] = int(X[nD + k, c])
    Rr, rk = R.rref()
    basis = []
    for i in range(rk):
        vec = [ratrec(int(Rr[i, k])) for k in range(N + 1)]
        basis.append(vec)
    print(f"N={N} {kind} support={support}: sizes={sizes} unknowns={nvar} equations={len(rows)}"
          f" nullity={nullity} nullity_r0={nullity - rk} dim r-space={rk}")
    for vec in basis:
        print("     r = [" + ", ".join("?" if x is None else str(x) for x in vec) + "]")
    sys.stdout.flush()


def main():
    NMAX = int(sys.argv[1])
    supports = sys.argv[2].split(',')
    kinds = sys.argv[3].split(',') if len(sys.argv) > 3 else ['live', 'all']
    for N in range(1, NMAX + 1):
        for kind in kinds:
            for support in supports:
                analyse(N, kind, support)


if __name__ == '__main__':
    main()
