"""chainface.py M K [Q]: the order-Q (default Q = 2^(M-1)) Fourier part of c_{K-M}(N) from the
local face formula at the CHAIN faces (../periods2/PROOFS.txt sections 1-3):
M of the K points form a chain x_1 = 0 (box mark, inner side x_1 > 0), x_{t+1} = (x_t + c_t)/2
(t = 1..n, n = M - 1, exact denominator 2^n, i.e. x_1 + c_1 odd), the other K - M points are free.
Contribution to the coefficient of e(N r/2^n):
   (1/2^n) sum_{chains, l : l a = r mod 2^n} A(chain) prod_{j<n} h(2^j l/2^n) (-h(l/2^n)),
   a = 2^n x_M (odd), A(chain) = sum over time placements of the signed volume of the valid
   free configurations (each halving column has at most one valid side, sign +1 for u <= 0).
Mirror chains (x_1 = 1) give identical functions of N (factor 2).
F = K - M = 0, 1, 2 free points (exact rational integration as in face.py).  x_1 = 0 is
handled as x_1 = eps, A(0) = 2 A(eps) - A(2 eps) (A is affine in small eps; checked with 3 eps).
"""
import sys
import cmath
import math
from fractions import Fraction as Fr
from itertools import combinations, product

sys.path.insert(0, '../periods2')
from face import sgn, breakpoints, cells2


def chain_values(bits, eps):
    v = [eps]
    for c in bits:
        v.append((v[-1] + c) / 2)
    return v


def weight(seq, cyc_pos, bits):
    """None or sign.  Column of x_1: ordinary (sum 0).  Halving columns t = 1..n."""
    M = len(cyc_pos)
    tight = {(cyc_pos[t - 1], cyc_pos[t]) for t in range(1, M)}
    role = {p: t for t, p in enumerate(cyc_pos)}
    sign = 1
    for j in range(len(seq)):
        s = sum(sgn(seq[i], seq[j]) for i in range(j) if (i, j) not in tight)
        if j not in role or role[j] == 0:
            if s != 0:
                return None
            continue
        cb = bits[role[j] - 1]
        opts = []
        for side in ('le', 'gt'):
            sig = (1 if side == 'le' else 0) if cb == 1 else (0 if side == 'le' else -1)
            if s + sig == 0:
                opts.append(side)
        if not opts:
            return None
        assert len(opts) == 1
        sign *= 1 if opts[0] == 'le' else -1
    return sign


def integrate_eps(v, bits, K):
    M = len(v)
    F = K - M
    A = Fr(0)
    for cyc_pos in combinations(range(K), M):
        free_pos = [p for p in range(K) if p not in cyc_pos]

        def build(z):
            seq = [None] * K
            for p, val in zip(cyc_pos, v):
                seq[p] = val
            for p, val in zip(free_pos, z):
                seq[p] = val
            return seq
        if F == 0:
            w = weight(build([]), list(cyc_pos), bits)
            if w:
                A += w
        elif F == 1:
            B = breakpoints(v)
            for x0, x1 in zip(B, B[1:]):
                w = weight(build([(x0 + x1) / 2]), list(cyc_pos), bits)
                if w:
                    A += w * (x1 - x0)
        elif F == 2:
            for (area, pt) in cells2(v):
                w = weight(build(list(pt)), list(cyc_pos), bits)
                if w:
                    A += w * area
        else:
            raise NotImplementedError
    return A


def integrate(bits, K):
    n = len(bits)
    # A(eps) is a polynomial of degree <= F in eps for small eps: interpolate at eps = e, 2e, ..
    F = K - len(bits) - 1
    e = Fr(1, 2 ** (n + 40))
    pts = [(j * e, integrate_eps(chain_values(bits, j * e), bits, K)) for j in range(1, F + 3)]

    def lag(xs, x0):
        tot = Fr(0)
        for i, (xi, yi) in enumerate(xs):
            w = Fr(1)
            for j, (xj, _) in enumerate(xs):
                if j != i:
                    w *= (x0 - xj) / (xi - xj)
            tot += w * yi
        return tot
    assert lag(pts[:-1], pts[-1][0]) == pts[-1][1], 'not polynomial of degree F in eps'
    return lag(pts[:-1], Fr(0))


def h(x):
    return 1 / (1 - cmath.exp(-2j * math.pi * float(x)))


def predicted(n, data, q):
    """coefficient of e(-N/q) (both mirrors included)."""
    P = 2 ** n
    tot = 0
    for a, A in data.items():
        if A == 0:
            continue
        for l in range(1, P, 2):
            if (Fr(l * a, P) + Fr(1, q)) % 1 != 0:
                continue
            p = 1
            for j in range(n):
                p *= h(Fr(2 ** j * l, P))
            tot += 2 * p * (-h(Fr(l, P))) * float(A) / P
    return tot


def all_chains(n):
    for bits in product((0, 1), repeat=n):
        if bits[0] != 1:
            continue
        x = Fr(0)
        for c in bits:
            x = (x + c) / 2
        yield bits, int(x * 2 ** n)


if __name__ == '__main__':
    M, K = int(sys.argv[1]), int(sys.argv[2])
    n = M - 1
    q = int(sys.argv[3]) if len(sys.argv) > 3 else 2 ** n
    data = {}
    for bits, a in all_chains(n):
        A = integrate(bits, K)
        data[a] = A
        if A:
            print(f'  word={"".join(map(str, bits))}  x_M={a}/2^{n}  A={A}', flush=True)
    print(f'M={M} K={K} q={q}: chain prediction, coefficient of e(-N/q) in c_{K-M} '
          f'(x (K-M)!) = {predicted(n, data, q) * math.factorial(K - M)}')
