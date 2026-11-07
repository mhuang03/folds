"""certify.py KMAX [KMIN]: certify that c_0(T(N,k)) has a nonzero Fourier component of exact order
q = 2^a (2^s - 1) for every a >= 1, s >= 2, a + s = k - 1, KMIN <= k <= KMAX.

Coefficient of e(-N/q) = sum over valid cycle + pendant chain vertices (Prop. 1.1, mixed.py).
Structures <-> pairs (u, j), u a unit mod q, 0 <= j < s; all valid time orders of (u, j) have the
same modulus M(u, j), and there are at most C(s-j+a, a) of them (Lemma 2.1).
  Path A (s >= 4, a >= 2): by Lemma 2.3 (main family) the pairs u = +-1, j = 0 contribute exactly
     2 X h h, of modulus 2 M(1,0); by Lemma 2.4 (rotation lemma) the pairs u = +-1 mod D, j >= 1
     contribute nothing.  Certified if  rest2 := sum_{other (u,j)} C(s-j+a, a) M(u,j)/M(1,0) < 2.
  Path B (otherwise): the pairs with C(s-j+a,a) M(u,j)/M(1,0) > TAU are rebuilt and all their
     valid time orders evaluated exactly (mixed.py); the others are bounded crudely.  Certified
     if |exact part| > crude tail.  (Rotation pairs are excluded from the tail only if s >= 4.)
Floating point: float64 throughout; the margins printed are the safety factors.
"""
import sys
import time
import math
from math import comb
import numpy as np
from topcheck import structure
from mixed import interleavings, vertex_term


def logfac(x):
    return -np.log(2 * np.abs(np.sin(np.pi * x)))


def scan(s, a, tau, block=1 << 21):
    """returns (sum over non-main non-excluded pairs of C*ratio [split into > tau and <= tau],
    list of (u, j, ratio) above tau)."""
    D = 2 ** s - 1
    q = 2 ** a * D
    cs = [D * 2 ** (i - 1) for i in range(1, a + 1)] + [2 ** e for e in range(s)]
    L0 = sum(logfac(c / q) for c in cs) + logfac(2 ** s / q)
    tail = 0.0
    top = []
    for start in range(1, q, block):
        u = np.arange(start, min(start + block, q), dtype=np.int64)
        u = u[(u % 2 == 1) & (np.gcd(u, D) == 1)]
        main = (u == 1) | (u == q - 1)
        rot = (((u % D) == 1) | ((u % D) == D - 1)) if s >= 4 else np.zeros(len(u), bool)
        L = np.zeros(len(u))
        for c in cs:
            L += logfac(((u * c) % q) / q)
        for j in range(s):
            r = np.exp(L + logfac(((u * 2 ** (s - j)) % q) / q) - L0)
            w = comb(s - j + a, a) * r
            if j == 0:
                excl = main
            else:
                excl = rot            # Lemma 2.4 (s >= 4); empty for s <= 3
            sel = (w > tau) & ~excl
            if j == 0:
                sel |= main
            tail += float(w[~sel & ~excl].sum())
            top += [(int(x), j, float(y)) for x, y in zip(u[sel], r[sel])]
    return tail, top


def exact(s, a, top):
    D = 2 ** s - 1
    q = 2 ** a * D
    cs = [D * 2 ** (i - 1) for i in range(1, a + 1)] + [2 ** e for e in range(s)] + [2 ** s]
    M0 = math.exp(-math.log(q) - sum(math.log(2 * abs(math.sin(math.pi * c / q))) for c in cs))
    tot = 0
    nval = 0
    for u, j, r in top:
        orb, z = structure(u, j, s, a)
        for y, lab in interleavings(orb, j, z):
            t, info = vertex_term(y, q)
            if t is not None:
                tot += t
                nval += 1
    return tot / M0, nval


def certify(s, a, verbose=False):
    t0 = time.time()
    if s >= 4 and a >= 2:
        tail, top = scan(s, a, tau=float('inf'))
        if tail < 2:
            return 'A', 2.0, tail, time.time() - t0
    for tau in (1e-3, 1e-5, 1e-7, 1e-9):
        tail, top = scan(s, a, tau)
        if len(top) > 300000:
            break
        ex, nv = exact(s, a, top)
        if abs(ex) > tail:
            return f'B(tau={tau:g},{len(top)} pairs,{nv} valid)', abs(ex), tail, time.time() - t0
    return 'FAILED', abs(ex), tail, time.time() - t0


if __name__ == '__main__':
    K = int(sys.argv[1])
    K0 = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    amin = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    for k in range(K0, K + 1):
        for s in range(2, k - amin):
            a = k - 1 - s
            how, main, tail, dt = certify(s, a)
            print(f'k={k:2d} s={s:2d} a={a:2d} q={2**a*(2**s-1):9d}  {how:40s} |main|/M0={main:.6g}  '
                  f'tail/M0<={tail:.4g}  margin={main / tail if tail else float("inf"):.3g}  ({dt:.0f}s)',
                  flush=True)
