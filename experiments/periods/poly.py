"""poly.py: the order-type polytopes, shared by the scripts in this directory.

A valid k-prefix x_1..x_k (panels of [1..N]) has an order type pi (pi[i] = rank of x_i) and,
by the window rule (../prefix/FINDINGS.txt section 4), a sign matrix sigma forced by pi:
sigma[i,j] (i < j) = +1 if x_j lies in the right arm of x_i (x_i < x_j, 2x_j <= N + x_i),
-1 if in the left arm (x_j < x_i, 2x_j > x_i), 0 otherwise.

With y = x/N every defining inequality is HOMOGENEOUS in (x, N), strict or not:
   x_i > 0, x_i <= N, x_u < x_v (pi-consecutive),
   +1: 2x_j <= N + x_i,  -1: 2x_j > x_i,  0 & up: 2x_j > N + x_i,  0 & down: 2x_j <= x_i.
So the class is (N * P) cap Z^k for the partially open rational polytope P (N = 1).

rows(pi) returns (a, c, strict) meaning a.y + c >= 0 (strict: > 0).
"""
from itertools import combinations


def forced_sigma(npi):
    """window rule for the LAST point of npi (ranks); returns {i: sign} for the earlier points."""
    K = len(npi)
    r = npi[-1]
    below = sorted([i for i in range(K - 1) if npi[i] < r], key=lambda i: -npi[i])  # nearest first
    above = sorted([i for i in range(K - 1) if npi[i] > r], key=lambda i: npi[i])
    A, B = len(above), len(below)
    s = {i: 0 for i in range(K - 1)}
    t = min(A, B)
    for i in below[:t]:
        s[i] = 1
    for i in above[:t]:
        s[i] = -1
    return s


def sigma_of(pi):
    sig = {}
    for j in range(1, len(pi)):
        sub = rerank(pi[:j + 1])
        for i, v in forced_sigma(sub).items():
            sig[(i, j)] = v
    return sig


def rerank(p):
    srt = sorted(p)
    return tuple(srt.index(v) + 1 for v in p)


def rows(pi, sig=None):
    K = len(pi)
    if sig is None:
        sig = sigma_of(pi)
    R = []

    def row(coef, c, strict, tag):
        a = [0] * K
        for i, v in coef:
            a[i] += v
        R.append((tuple(a), c, strict, tag))
    for i in range(K):
        row([(i, 1)], 0, True, ('zero', i))          # y_i > 0
        row([(i, -1)], 1, False, ('one', i))         # y_i <= 1
    order = sorted(range(K), key=lambda i: pi[i])
    for u, v in zip(order, order[1:]):
        row([(v, 1), (u, -1)], 0, True, ('eq', u, v))  # y_v > y_u
    for (i, j), s in sorted(sig.items()):
        up = pi[j] > pi[i]
        if s == 1:
            row([(j, -2), (i, 1)], 1, False, ('half1', i, j))   # 2y_j <= 1 + y_i
        elif s == -1:
            row([(j, 2), (i, -1)], 0, True, ('half0', i, j))    # 2y_j > y_i
        elif up:
            row([(j, 2), (i, -1)], -1, True, ('half1', i, j))   # 2y_j > 1 + y_i
        else:
            row([(j, -2), (i, 1)], 0, False, ('half0', i, j))   # 2y_j <= y_i
    return R


def extensions(pi):
    K = len(pi) + 1
    for r in range(1, K + 1):
        yield tuple(p + (p >= r) for p in pi) + (r,)


def mirror(pi):
    K = len(pi)
    return tuple(K + 1 - p for p in pi)
