"""face.py M K [Q]: the order-Q (default Q = 2^(M-1) - 1) Fourier part of c_{K-M}(N), the
coefficient of N^(K-M) in T(N,K), from the LOCAL FACE FORMULA (PROOFS.txt section 3):

The codimension-M faces carrying a factor 2^(M-1) - 1 (with a primitive prime) are: M of the K
points (the "cycle", in time order) sit at an orbit vertex of the M-point problem, x_{i_1} =
theta, consecutive cycle points halve (x_{i_{t+1}} = (x_{i_t} + c_t)/2), x_{i_M} = x_{i_1}; the
other K - M points are free.  For a free configuration z the valid local cells form a single
cell or none (each cycle column has at most one valid side), with weight
   sign(z) * prod_t h(theta_t) * (-g or -h)(l/D)   (Q-factor by the side of x_{i_M} vs x_{i_1}),
so the face sum is
   (1/D) sum_l e(N l theta) prod_{j<M-1} h(2^j l/D) * ( -A_above g(l/D) - A_below h(l/D) ),
   A_above/below(theta) = sum over time placements of the integral over z in (0,1)^(K-M) of
                          sign(z) [x_{i_M} above / below x_{i_1}],
h(x) = 1/(1 - e(-x)), g(x) = 1/(1 - e(x)).  The integrals are exact (rational arithmetic):
K - M = 0, 1, 2 supported.  Output: A_above, A_below per orbit vertex theta = a/D (all a with
exact period M - 1, valid or not), and the predicted Laurent coefficient at zeta = e(1/Q),
comparable with fourier2.py at pole order K + 1 - M.
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations
import cmath
import math


def sgn(x, c):
    """sign of the later point c relative to the earlier point x (generic)."""
    if x < c:
        if 2 * c < 1 + x:
            return 1
        if 2 * c == 1 + x:
            raise ValueError
        return 0
    if c == x:
        raise ValueError
    if 2 * c > x:
        return -1
    if 2 * c == x:
        raise ValueError
    return 0


def orbit(M, a):
    D = 2 ** (M - 1) - 1
    x1 = Fr(a, D)
    orb = [x1]
    for _ in range(M - 1):
        orb.append((2 * orb[-1]) % 1)
    if len(set(orb[:-1])) != M - 1:
        return None
    v = [orb[M - j] for j in range(1, M + 1)]
    bits = [int(2 * v[t] - v[t - 1]) for t in range(1, M)]
    return v, bits


def weight(seq, cyc_pos, bits):
    """seq: values in time order; cyc_pos: time indices of the cycle points (in cycle order).
    Returns None (no valid cell) or (sign, 'above'/'below')."""
    M = len(cyc_pos)
    tight = {(cyc_pos[t - 1], cyc_pos[t]) for t in range(1, M)} | {(cyc_pos[0], cyc_pos[-1])}
    role = {p: t for t, p in enumerate(cyc_pos)}
    sign = 1
    qside = None
    for j in range(len(seq)):
        s = sum(sgn(seq[i], seq[j]) for i in range(j) if (i, j) not in tight)
        if j not in role or role[j] == 0:
            if s != 0:
                return None
            continue
        t = role[j]
        cb = bits[t - 1]
        if t < M - 1:
            opts = []
            for side in ('le', 'gt'):
                sig = (1 if side == 'le' else 0) if cb == 1 else (0 if side == 'le' else -1)
                if s + sig == 0:
                    opts.append(side)
            if not opts:
                return None
            assert len(opts) == 1
            sign *= 1 if opts[0] == 'le' else -1
        else:
            opts = []
            for side in ('le', 'gt'):
                sig = (1 if side == 'le' else 0) if cb == 1 else (0 if side == 'le' else -1)
                for qs, qv in (('above', 1), ('below', -1)):
                    if s + sig + qv == 0:
                        opts.append((side, qs))
            if not opts:
                return None
            assert len(opts) == 1
            sign *= 1 if opts[0][0] == 'le' else -1
            qside = opts[0][1]
    return sign, qside


def breakpoints(vals):
    B = {Fr(0), Fr(1)}
    for v in vals:
        for b in (v, v / 2, (1 + v) / 2, 2 * v, 2 * v - 1):
            if 0 <= b <= 1:
                B.add(b)
    return sorted(B)


def integrate(v, bits, K):
    """returns (A_above, A_below) as Fractions."""
    M = len(v)
    F = K - M
    Aab = {'above': Fr(0), 'below': Fr(0)}
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
                Aab[w[1]] += w[0]
        elif F == 1:
            B = breakpoints(v)
            for x0, x1 in zip(B, B[1:]):
                w = weight(build([(x0 + x1) / 2]), list(cyc_pos), bits)
                if w:
                    Aab[w[1]] += w[0] * (x1 - x0)
        elif F == 2:
            for (cell_area, pt) in cells2(v):
                w = weight(build(list(pt)), list(cyc_pos), bits)
                if w:
                    Aab[w[1]] += w[0] * cell_area
        else:
            raise NotImplementedError
    return Aab['above'], Aab['below']


_cells_cache = {}


def cells2(v):
    """trapezoidal decomposition of (0,1)^2 by all lines z2 = a z1 + b relevant to the sign
    function: z2 = const (breakpoints of v), z2 = z1, 2 z1, 2 z1 - 1, z1/2, (1 + z1)/2, and
    the vertical lines z1 = breakpoints of v.  Returns [(area, interior point)]."""
    key = tuple(v)
    if key in _cells_cache:
        return _cells_cache[key]
    Bv = breakpoints(v)
    lines = [(Fr(0), b) for b in Bv]
    lines += [(Fr(1), Fr(0)), (Fr(2), Fr(0)), (Fr(2), Fr(-1)), (Fr(1, 2), Fr(0)), (Fr(1, 2), Fr(1, 2))]
    xs = set(Bv)
    for (a1, b1), (a2, b2) in combinations(lines, 2):
        if a1 != a2:
            x = (b2 - b1) / (a1 - a2)
            if 0 < x < 1:
                xs.add(x)
    xs = sorted(xs)
    out = []
    for x0, x1 in zip(xs, xs[1:]):
        xm = (x0 + x1) / 2
        ls = sorted({(a * xm + b, a, b) for a, b in lines if 0 <= a * xm + b <= 1})
        # also clip: lines within [0,1] on the whole slab (no crossing inside the slab)
        for (y0, a0, b0), (y1, a1, b1) in zip(ls, ls[1:]):
            if y1 == y0:
                continue
            area = (x1 - x0) * (((a1 - a0) * x0 + b1 - b0) + ((a1 - a0) * x1 + b1 - b0)) / 2
            out.append((area, (xm, (y0 + y1) / 2)))
    _cells_cache[key] = out
    return out


def h(x):
    return 1 / (1 - cmath.exp(-2j * math.pi * float(x)))


def g(x):
    return 1 / (1 - cmath.exp(2j * math.pi * float(x)))


def predicted(M, data, q):
    """Laurent coefficient at zeta = e(1/q) (= coefficient of e(-N/q))."""
    D = 2 ** (M - 1) - 1
    tot = 0
    for a, (Aa, Ab) in data.items():
        if Aa == 0 and Ab == 0:
            continue
        for l in range(1, D):
            if (Fr(l * a, D) + Fr(1, q)) % 1 != 0:
                continue
            p = 1
            for j in range(M - 1):
                p *= h(Fr(2 ** j * l, D))
            tot += p * (-float(Aa) * g(Fr(l, D)) - float(Ab) * h(Fr(l, D))) / D
    return tot


if __name__ == '__main__':
    M, K = int(sys.argv[1]), int(sys.argv[2])
    D = 2 ** (M - 1) - 1
    q = int(sys.argv[3]) if len(sys.argv) > 3 else D
    data = {}
    for a in range(1, D):
        ob = orbit(M, a)
        if ob is None:
            continue
        v, bits = ob
        Aa, Ab = integrate(v, bits, K)
        data[a] = (Aa, Ab)
        if Aa or Ab:
            print(f'  a={a:4d}/{D} bits={"".join(map(str, bits))}  A_above={Aa}  A_below={Ab}', flush=True)
    print(f'M={M} K={K} q={q}: predicted coefficient of e(-N/q) in c_{K-M} (x (K-M)!) = '
          f'{predicted(M, data, q) * math.factorial(K - M)}')
