"""ehrhart.py K [shard i/n]: EXACT quasi-polynomial T(N,K) via Normaliz (PyNormaliz).

T(N,K) = sum over classes (pi, sigma) of #{lattice points of P_{pi,sigma}(N)}, where pi is the
order type of x_1..x_K and sigma_ij (i<j) is the sign of x_j relative to x_i's arms
(+1 right arm, -1 left arm, 0 neither) -- exactly the classification of pieces.c.  Validity
is "every column of sigma sums to 0".  The classes partition the valid sequences, so the sum
is exact whether or not sigma is forced by pi (the window rule says it is).

Each class is the set of integer points (x, N) of ONE rational polyhedron Q in R^{K+1}
(all inequalities have integer coefficients, strict ones are written as >= ... + 1):
   1 <= x_i <= N,  x ordered as pi,
   sigma=+1: x_i+1 <= x_j, 2x_j <= N + x_i;     sigma=-1: x_j+1 <= x_i, 2x_j >= x_i + 1;
   sigma= 0: 2x_j >= N + x_i + 1 if x_j > x_i,  2x_j <= x_i if x_j < x_i.
Graded by N, the Hilbert series of Q (Normaliz, inhomogeneous input) is sum_N #P(N) t^N, and
its Hilbert quasi-polynomial is the Ehrhart-type quasi-polynomial of the class.  Summing the
rational generating functions over the classes gives sum_N T(N,K) t^N exactly.

Classes are generated step by step (rank of the new point + balanced choice of the earlier
points in its two arms), pruned by exact emptiness: a class with no lattice points for any N
has no extensions with lattice points either, so we keep only classes whose Hilbert series
is nonzero.

Output: classes_K.txt  (pi, sigma, numerator, denominator exponents, shift) per class.
"""
import sys
import json
from itertools import combinations
import PyNormaliz as PN


def rows(K, pi, sig):
    """inhomogeneous inequalities [a_1..a_K, a_N, b] meaning a.x + a_N N + b >= 0."""
    R = []

    def row(coef, cN, b):
        a = [0] * K
        for i, c in coef:
            a[i] += c
        R.append(a + [cN, b])
    for i in range(K):
        row([(i, 1)], 0, -1)        # x_i >= 1
        row([(i, -1)], 1, 0)        # x_i <= N
    order = sorted(range(K), key=lambda i: pi[i])
    for u, v in zip(order, order[1:]):
        row([(v, 1), (u, -1)], 0, -1)   # x_v >= x_u + 1
    for (i, j), s in sig.items():
        up = pi[j] > pi[i]
        if s == 1:      # x_i < x_j (from order), 2x_j <= N + x_i
            row([(j, -2), (i, 1)], 1, 0)
        elif s == -1:   # x_j < x_i, 2x_j >= x_i + 1
            row([(j, 2), (i, -1)], 0, -1)
        elif up:        # 2x_j >= N + x_i + 1
            row([(j, 2), (i, -1)], -1, -1)
        else:           # 2x_j <= x_i
            row([(j, -2), (i, 1)], 0, 0)
        if s == 1:
            assert up
        if s == -1:
            assert not up
    return R


def nonempty(K, pi, sig):
    C = PN.Cone(inhom_inequalities=rows(K, pi, sig), grading=[[0] * K + [1]])
    num, den, shift = C.HilbertSeries()
    return any(num), (num, den, shift)


def extensions(pi, sig, K):
    for r in range(1, K + 1):
        npi = tuple(p + (p >= r) for p in pi) + (r,)
        below = [i for i in range(K - 1) if npi[i] < r]
        above = [i for i in range(K - 1) if npi[i] > r]
        for t in range(0, min(len(below), len(above)) + 1):
            for B in combinations(below, t):
                for A in combinations(above, t):
                    s = dict(sig)
                    for i in range(K - 1):
                        s[(i, K - 1)] = 1 if i in B else (-1 if i in A else 0)
                    yield npi, s


def run(KMAX, shard=(0, 1)):
    classes = [((1,), {})]
    data = None
    for K in range(2, KMAX + 1):
        new = []
        cand = list(extensions(pi, sig, K) for pi, sig in classes)
        cand = [c for g in cand for c in g]
        if K == KMAX:
            cand = cand[shard[0]::shard[1]]
        for npi, s in cand:
            ok, ser = nonempty(K, npi, s)
            if ok:
                new.append((npi, s, ser))
        classes = [(p, s) for p, s, _ in new]
        data = new
        types = {}
        for p, s in classes:
            types.setdefault(p, []).append(s)
        print(f'k={K}: {len(cand)} candidates, {len(classes)} nonempty classes, '
              f'{len(types)} order types, {sum(len(v) > 1 for v in types.values())} with >1 class',
              file=sys.stderr, flush=True)
    return data


if __name__ == '__main__':
    K = int(sys.argv[1])
    shard = (0, 1)
    if len(sys.argv) > 2:
        shard = tuple(map(int, sys.argv[2].split('/')))
    data = run(K, shard)
    suffix = '' if shard == (0, 1) else f'_{shard[0]}of{shard[1]}'
    with open(f'classes_{K}{suffix}.json', 'w') as f:
        for pi, s, (num, den, shift) in data:
            f.write(json.dumps({'pi': list(pi),
                                'sig': [[i, j, v] for (i, j), v in sorted(s.items())],
                                'num': [int(x) for x in num], 'den': [int(x) for x in den],
                                'shift': int(shift)}) + '\n')
