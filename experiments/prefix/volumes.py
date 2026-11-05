"""volumes.py PIECESFILE K: exact leading coefficient c_K = lim T(N,K)/N^K as a sum of
exact volumes of one polytope per admissible order type.

For order type pi with (forced) sign matrix sigma, the continuous polytope (N = 1, x real) is
   0 <= x <= 1,   x ordered as pi,
   sigma_ij = +1 :  x_i <= x_j,  2 x_j - x_i <= 1
   sigma_ij = -1 :  x_j <= x_i,  2 x_j - x_i >= 0
   sigma_ij =  0 :  2 x_j - x_i >= 1 if x_j > x_i,  2 x_j - x_i <= 0 if x_j < x_i.
Vertices are found numerically (scipy halfspace intersection), snapped to rationals and checked
exactly (each must satisfy all inequalities exactly and lie on >= K of them); the volume is then
computed exactly from a triangulation of the hull (cone over triangulated facets from the
rational centroid)."""
import sys
from fractions import Fraction as F
from math import factorial
import numpy as np
from scipy.optimize import linprog
from scipy.spatial import HalfspaceIntersection, ConvexHull

fn, K = sys.argv[1], int(sys.argv[2])
npairs = K * (K - 1) // 2
nsig = 3 ** npairs
keys = sorted({int(l.split()[1]) for l in open(fn)})


def decode(key):
    code, s = divmod(key, nsig)
    lehmer = []
    for i in reversed(range(K)):
        lehmer.append(code % (K - i))
        code //= (K - i)
    lehmer.reverse()
    avail = list(range(1, K + 1))
    pi = [avail.pop(r) for r in lehmer]
    sig = []
    for _ in range(npairs):
        sig.append(s % 3 - 1)
        s //= 3
    sig.reverse()
    pairs = [(i, j) for j in range(1, K) for i in range(j)]
    return pi, dict(zip(pairs, sig))


def ineqs(pi, sig):
    """rows (a, b) meaning a.x <= b."""
    R = []

    def row(coef, b):
        a = [0] * K
        for i, c in coef:
            a[i] += c
        R.append((a, b))
    for i in range(K):
        row([(i, -1)], 0)
        row([(i, 1)], 1)
    order = sorted(range(K), key=lambda i: pi[i])
    for u, v in zip(order, order[1:]):
        row([(u, 1), (v, -1)], 0)
    for (i, j), s in sig.items():
        up = pi[j] > pi[i]
        if s == 1:
            row([(j, 2), (i, -1)], 1)
        elif s == -1:
            row([(j, -2), (i, 1)], 0)
        elif up:
            row([(j, -2), (i, 1)], -1)
        else:
            row([(j, 2), (i, -1)], 0)
    return R


def det(M):
    M = [r[:] for r in M]
    n = len(M)
    d = F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return F(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return d


def volume(R):
    A = np.array([a for a, b in R], float)
    b = np.array([b for a, b in R], float)
    norms = np.linalg.norm(A, axis=1)
    # Chebyshev centre: max t s.t. A x + t |A| <= b
    res = linprog(np.r_[np.zeros(K), -1], A_ub=np.c_[A, norms], b_ub=b,
                  bounds=[(None, None)] * K + [(0, None)], method='highs')
    if res.status != 0 or res.x[-1] < 1e-9:
        return F(0)
    c = res.x[:K]
    hs = HalfspaceIntersection(np.c_[A, -b], c)
    pts = []
    for v in hs.intersections:
        q = tuple(F(float(t)).limit_denominator(100000) for t in v)
        tight = 0
        for a, bb in R:
            s = sum(F(ai) * qi for ai, qi in zip(a, q))
            assert s <= bb, 'snapped vertex violates an inequality'
            tight += s == bb
        assert tight >= K, 'snapped vertex is not a vertex'
        pts.append(q)
    pts = sorted(set(pts))
    hull = ConvexHull(np.array([[float(t) for t in p] for p in pts]), qhull_options='Qt')
    cen = tuple(sum(p[i] for p in pts) / len(pts) for i in range(K))
    vol = F(0)
    for simp in hull.simplices:
        M = [[pts[s][i] - cen[i] for i in range(K)] for s in simp]
        vol += abs(det(M))
    return vol / factorial(K)


total = F(0)
out = []
for key in keys:
    pi, sig = decode(key)
    v = volume(ineqs(pi, sig))
    out.append((''.join(map(str, pi)), v))
    total += v
for p, v in out:
    if K <= 4:
        print(p, v)
print('K =', K, 'classes', len(keys), ' c_K =', total, '=', float(total), ' K!*c_K =', total * factorial(K))
