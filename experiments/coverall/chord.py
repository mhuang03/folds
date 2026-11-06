"""chord.py: exact (Fraction) model of Lean famCons and the chord structure for a direction.
Used for exploration: python3 chord.py N u u' o f p q."""
from fractions import Fraction as F
import sys


def params(N, y, f):
    if f == 0:
        return (N + 2, y, 0, 1, (N + 2) // 2, 2)
    if f == 1:
        return (N, y - 2, 0, 1, (N + 1) // 2, 1)
    return (N, y - 2, 1, 0, N // 2, 2)


def famcons(K, L, R, al, be, smax, amin):
    """13 affine forms (A, C, D) as in Lean famCons (exact Fractions)."""
    U = [(F(K, L), F(0), F(-al, L)), (F(0), F(K, R), F(-be, R)), (F(0), F(0), F(smax))]
    Lw = [(F(K, L + 1), F(0), F(1 - al, L + 1)), (F(0), F(K, R + 1), F(1 - be, R + 1)),
          (F(0), F(0), F(R)), (F(0), F(0), F(2))]
    cs = []
    for u in U:
        for l in Lw:
            cs.append((u[0] - l[0], u[1] - l[1], u[2] - l[2] - 1))
    cs.append((F(1), F(0), F(-amin)))
    return cs


def cons(N, u, up, o, f):
    x, y = (up, u) if o else (u, up)
    return famcons(x=None, **{}) if False else famcons(*paramsL(N, x, y, f))


def paramsL(N, x, y, f):
    K, R, al, be, smax, amin = params(N, y, f)
    return (K, x, R, al, be, smax, amin)


def ev(c, a, cc):
    return c[0] * a + c[1] * cc + c[2]


def parok_check(cs, Pa, Pc, d, p1, q1, p2, q2):
    assert p1 * q2 - p2 * q1 == 1
    corners = [(Pa, Pc), (Pa + p1, Pc + q1), (Pa + p2 + d * p1, Pc + q2 + d * q1),
               (Pa + p1 + p2 + d * p1, Pc + q1 + q2 + d * q1)]
    worst = None
    for i, c in enumerate(cs):
        for k, (a, cc) in enumerate(corners):
            v = ev(c, a, cc)
            if worst is None or v < worst[0]:
                worst = (v, i, k)
    return worst


if __name__ == "__main__":
    N, u, up, o, f, p, q = map(int, sys.argv[1:8])
    x, y = (up, u) if o else (u, up)
    cs = famcons(*paramsL(N, x, y, f))
    for i, c in enumerate(cs):
        print(i, c, float(c[0] * p + c[1] * q))
