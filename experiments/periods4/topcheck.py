"""topcheck.py S A [TAU]: certified nonvanishing of the exact-order q = 2^A (2^S - 1) component of
c_0(T(N, S+A+1)) by "exact top + crude tail".

Every structure (cycle + pendant chain, mixed.py) is indexed by (u, j): u = (q z_a)^(-1) mod q a
unit, j in 0..S-1 the attachment index (PROOFS.txt section 2).  Its valid time orders all have
the same modulus M(u, j) (closed form, census.py) and there are at most C(S-j+A, A) of them.
  * pairs with C(S-j+A, A) M(u,j)/M(1,0) > TAU: the structure is rebuilt from (u, j) and all its
    valid time orders are enumerated and evaluated exactly (mixed.py);
  * all other pairs: |contribution| <= C(S-j+A, A) M(u, j)   (tail).
The component is nonzero if |exact part| > tail.  Output: exact part / M(1,0), tail / M(1,0),
and the list of the top structures with their valid time orders.
"""
import sys
import math
import numpy as np
from fractions import Fraction as Fr
from math import comb
from mixed import interleavings, vertex_term, T, word


def logfac(x):
    return -np.log(2 * np.abs(np.sin(np.pi * x)))


def ratios(s, a, block=1 << 22):
    """yield (u array, j, ratio array) over all units u != 0 mod q."""
    D = 2 ** s - 1
    q = 2 ** a * D
    cs = [D * 2 ** (i - 1) for i in range(1, a + 1)] + [2 ** e for e in range(s)]
    L0 = sum(logfac(c / q) for c in cs) + logfac(2 ** s / q)
    for start in range(1, q, block):
        u = np.arange(start, min(start + block, q), dtype=np.int64)
        u = u[(u % 2 == 1) & (np.gcd(u, D) == 1)]
        L = np.zeros(len(u))
        for c in cs:
            L += logfac(((u * c) % q) / q)
        for j in range(s):
            yield u, j, np.exp(L + logfac(((u * 2 ** (s - j)) % q) / q) - L0)


def structure(u, j, s, a):
    D = 2 ** s - 1
    q = 2 ** a * D
    N = pow(int(u), -1, q)
    z = [Fr(N, q)]
    for _ in range(a - 1):
        z.append(T(z[-1]))
    z = z[::-1]                       # z_1 .. z_a
    P = T(z[0])                       # attachment value x_{t_j}
    theta = P
    for _ in range(j):
        theta = T(theta)
    orb = [theta]
    for i in range(s):
        x = orb[-1]
        orb.append(next(p for p in (x / 2, (x + 1) / 2) if period_s(p, s)))
    assert orb[j] == P and orb[-1] == theta
    return orb, z


def period_s(x, s):
    y = x
    for _ in range(s):
        y = T(y)
    return y == x


def run(s, a, tau=1e-3, verbose=True):
    D = 2 ** s - 1
    q = 2 ** a * D
    top = []
    tail = 0.0
    for u, j, r in ratios(s, a):
        w = comb(s - j + a, a)
        sel = w * r > tau
        tail += float((w * r[~sel]).sum())
        top += [(int(x), j, float(y)) for x, y in zip(u[sel], r[sel])]
    M0 = None
    exact = 0
    rows = []
    for u, j, r in sorted(top, key=lambda t: -t[2]):
        orb, z = structure(u, j, s, a)
        tot = 0
        words = []
        for y, lab in interleavings(orb, j, z):
            t, info = vertex_term(y, q)
            if t is None:
                continue
            tot += t
            words.append(word(lab) + ('*' if len(info[0][1]) != len([1 for _ in y]) else ''))
        exact += tot
        rows.append((u if u < q // 2 else u - q, j, r, len(words), tot, words))
    # M(1,0) from the closed form
    cs = [D * 2 ** (i - 1) for i in range(1, a + 1)] + [2 ** e for e in range(s)] + [2 ** s]
    M0 = math.exp(-math.log(q) - sum(math.log(2 * abs(math.sin(math.pi * c / q))) for c in cs))
    if verbose:
        for u, j, r, nv, tot, words in rows:
            if nv:
                print(f'   u={u:7d} j={j:2d} ratio={r:.3g} V={nv:3d} sum/M0={tot / M0:.6f}  {words[:6]}')
        print(f'   ({len(rows)} top pairs, {sum(1 for x in rows if x[3])} with valid time orders)')
    return exact / M0, tail, rows


if __name__ == '__main__':
    s, a = int(sys.argv[1]), int(sys.argv[2])
    tau = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-3
    ex, tl, _ = run(s, a, tau)
    print(f'(s,a)=({s},{a}) q={2**a*(2**s-1)} exact top / M0 = {ex:.8f}  |.| = {abs(ex):.6f}  '
          f'tail / M0 <= {tl:.3g}  {"NONZERO" if abs(ex) > tl else "undecided"}')
