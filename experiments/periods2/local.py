"""local.py: the LOCAL (vertex) formula for Fourier components of the constant term of T(N,k).

Setting (../periods/PROOFS.txt): T(N,k) = sum over classes c of #(Z^k cap N P_c), P_c half-open.
At a vertex v let the tight constraints be k independent rows u_r(y) = a_r . y - b_r (a_r
integer, b_r in {0,1}); M = (a_r).  The classes whose closure contains v have as tangent cones
the VALID open orthants of the local arrangement (with the boundary conventions of the class
inequalities).  Brion's theorem plus the character expansion of the coset u in M Z^k - N b give
   periodic part of v's contribution to c_0 = (1/D) sum_{w in M^{-T}Z^k/Z^k, all w_r != 0}
                                                 e(N <w,b>) Cell(w),
   Cell(w) = sum_{valid orthants eps} prod_r F_r^{eps_r}(w_r),
F = 1-dim lattice sums sum_{u in side} e(w u) (analytic since w_r is not in Z).
Boundary conventions:  halving 2y_j - y_i - c: the boundary belongs to the side u <= 0;
equality y_a - y_b: to neither side; box y_i > 0 (u = y_i): excluded; y_i <= 1 (u = y_i - 1):
included, and only the inner side is valid.

python3 local.py K Q [chain|orbit]: Laurent coefficient A at zeta = e(1/Q) (= coefficient of
e(-N/Q) in c_0), per vertex and total; comparable with ../periods/fourier.py.
"""
from fractions import Fraction as Fr
from itertools import product
import cmath
import math

TAU = 2 * math.pi


def e(x):
    return cmath.exp(1j * TAU * float(x))


def side_sum(theta, sign, closed):
    """sum over u in Z on side sign (+1: u>0 / u>=0, -1: u<0 / u<=0) of e(theta u)."""
    z = e(theta if sign > 0 else -theta)
    return (1 / (1 - z)) if closed else (z / (1 - z))


def phi(x, c):
    if x < c < (1 + x) / 2:
        return 1
    if x / 2 < c < x:
        return -1
    if c in (x, (1 + x) / 2, x / 2):
        raise ValueError('not generic')
    return 0


def valid(y):
    if any(not (0 < t < 1) for t in y):
        return False
    for j in range(1, len(y)):
        if sum(phi(y[i], y[j]) for i in range(j)) != 0:
            return False
    return True


def tight_rows(v):
    k = len(v)
    R = []
    for i in range(k):
        if v[i] == 0:
            R.append((tuple(1 if t == i else 0 for t in range(k)), 0, 'box0'))
        if v[i] == 1:
            R.append((tuple(1 if t == i else 0 for t in range(k)), 1, 'box1'))
    for i in range(k):
        for j in range(i + 1, k):
            for c in (0, 1):
                if 2 * v[j] - v[i] == c:
                    a = [0] * k
                    a[j] += 2
                    a[i] -= 1
                    R.append((tuple(a), c, 'half'))
            if v[i] == v[j]:
                a = [0] * k
                a[j] += 1
                a[i] -= 1
                R.append((tuple(a), 0, 'eq'))
    return R


def solve(M, rhs):
    n = len(M)
    A = [[Fr(x) for x in M[r]] + [Fr(rhs[r])] for r in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [A[r][n] / A[r][r] for r in range(n)]


def transpose(M):
    return [list(r) for r in zip(*M)]


def characters(M):
    """the group M^{-T} Z^k / Z^k as a list of tuples of Fractions mod 1."""
    k = len(M)
    MT = transpose(M)
    gens = []
    for i in range(k):
        rhs = [0] * k
        rhs[i] = 1
        gens.append(tuple(x % 1 for x in solve(MT, rhs)))
    G = {tuple([Fr(0)] * k)}
    frontier = list(G)
    while frontier:
        nf = []
        for g in frontier:
            for h in gens:
                s = tuple((a + b) % 1 for a, b in zip(g, h))
                if s not in G:
                    G.add(s)
                    nf.append(s)
        frontier = nf
    return sorted(G)


def local_cells(v, eta=Fr(1, 10 ** 12)):
    k = len(v)
    R = tight_rows(v)
    assert len(R) == k, ('non-simple vertex', v, R)
    M = [list(r[0]) for r in R]
    b = [r[1] for r in R]
    kinds = [r[2] for r in R]
    cells = []
    for eps in product((1, -1), repeat=k):
        if any(kd == 'box0' and s < 0 for kd, s in zip(kinds, eps)):
            continue
        if any(kd == 'box1' and s > 0 for kd, s in zip(kinds, eps)):
            continue
        rhs = [b[r] + eps[r] * eta * (1 + Fr(r, 7)) for r in range(k)]
        y = solve(M, rhs)
        if valid(y):
            cells.append(eps)
    return M, b, kinds, cells


def vertex_modes(v):
    """{mode (Fraction <w,b> mod 1): coefficient} over the w with all w_r != 0, i.e. the vertex's
    contribution sum_mode coef * e(N*mode) to the constant term; and the number of valid cells."""
    M, b, kinds, cells = local_cells(v)
    k = len(v)
    modes = {}
    if not cells:
        return modes, 0
    chars = characters(M)
    D = len(chars)
    for w in chars:
        if any(x == 0 for x in w):
            continue
        tot = 0
        for eps in cells:
            p = 1
            for r in range(k):
                kd = kinds[r]
                closed = (eps[r] < 0) if kd == 'half' else (kd == 'box1')
                p *= side_sum(w[r], eps[r], closed)
            tot += p
        mode = sum(wr * br for wr, br in zip(w, b)) % 1
        modes[mode] = modes.get(mode, 0) + tot / D
    return modes, len(cells)


def orbit_vertices(k, exact=True):
    """x_1 = a/(2^(k-1)-1), x_j = T^(k-j) x_1 (T = doubling mod 1), so x_k = x_1."""
    D = 2 ** (k - 1) - 1
    out = []
    for a in range(1, D):
        x1 = Fr(a, D)
        orb = [x1]
        for _ in range(k - 1):
            orb.append((2 * orb[-1]) % 1)
        assert orb[-1] == x1
        if exact and len(set(orb[:-1])) != k - 1:
            continue
        out.append(tuple(orb[k - j] for j in range(1, k + 1)))
    return out


def chain_vertices(k):
    """x_1 in {0,1}, x_{j+1} = (x_j + c_j)/2, exact denominator 2^(k-1)."""
    out = []
    for x1 in (Fr(0), Fr(1)):
        for bits in product((0, 1), repeat=k - 1):
            if (x1 + bits[0]) % 2 == 0:
                continue
            y = [x1]
            for c in bits:
                y.append((y[-1] + c) / 2)
            out.append(tuple(y))
    return out


def fmt(v):
    return '(' + ', '.join(str(x) for x in v) + ')'


if __name__ == '__main__':
    import sys
    k = int(sys.argv[1])
    q = int(sys.argv[2])
    fam = sys.argv[3] if len(sys.argv) > 3 else ('chain' if q & (q - 1) == 0 else 'orbit')
    verts = chain_vertices(k) if fam == 'chain' else orbit_vertices(k, exact=False)
    tot = 0
    target = Fr(-1, q) % 1
    for v in verts:
        try:
            modes, nc = vertex_modes(v)
        except AssertionError as ex:
            print('skip', ex)
            continue
        c = modes.get(target, 0)
        if nc:
            print(fmt(v), 'cells', nc, 'A =', c)
        tot += c
    print('total A at zeta=e(1/q):', tot)
