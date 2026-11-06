"""keys.py: the key conditions of the edge certificates (see PROOFS.txt) as exact rational
functions, plus the old regions D, B (regions.c semantics).  All functions take (N, u, up) with
u <= up; o = 1 orientation (x, y) = (up, u)."""
from fractions import Fraction as F


def edge4_keys(K, L, R, al, be, s0, amin, p, q):
    """f4-edge, w1 = (p, q).  Returns list of (name, value) whose nonnegativity is the key
    condition set (s0 a lower bound of smax)."""
    D = q * (L + 1) - p * R
    if D <= 0 or q * L < p * (R + 1):
        return [("regime", F(-1))]
    s8 = F(s0) - 1 - F(K * p, L + 1)
    s9 = (F(s0) - 1) * (R + 1) - K * q - 1
    s9 = s9 / R - 1
    out = []
    for nm, s1 in (("8", s8), ("9", s9)):
        s = s1 - F(K, D)
        P, Q = K * p, K * q
        out.append(("chord" + nm, (s * (L + 1) - 1 + P) * (R + 1) - ((s + 1) * R + 1 + Q) * L - L * (R + 1)))
        out.append(("bot" + nm, s - (L + 1)))
        out.append(("botR" + nm, s - (R + 1)))
        out.append(("amin" + nm, s * (L + 1) + al - 1 - amin * K))
    out.append(("s0", F(s0) - R - 1))
    return out


def edge1_keys(K, L, R, al, be, s0, amin, p, q):
    D = p * (R + 1) - q * L
    if D <= 0 or p * R < q * (L + 1):
        return [("regime", F(-1))]
    t8 = ((F(s0) - 1) * (L + 1) - K * p - 1) / L - 1
    t9 = F(s0) - 1 - F(K * q, R + 1)
    out = []
    for nm, t3 in (("8", t8), ("9", t9)):
        t = t3 - F(K, D)
        P, Q = K * p, K * q
        out.append(("chord" + nm, (t * (R + 1) - 1 + Q) * (L + 1) - ((t + 1) * L + 1 + P) * R - R * (L + 1)))
        out.append(("bot" + nm, t - (L + 1)))
        out.append(("botR" + nm, t - (R + 1)))
        out.append(("amin" + nm, (t + 1) * L + al - amin * K))
    out.append(("s0", F(s0) - R - 1))
    return out


def famZ(N, x, y):
    M = N + 2
    return (M, x, y, 0, 1, F(M - 1, 2), 2)


def famX0(N, x, y):
    return (N, x, y - 2, 0, 1, F(N, 2), 1)


def famX1(N, x, y):
    return (N, x, y - 2, 1, 0, F(N - 1, 2), 2)


def certA(N, u, up):
    return edge4_keys(*famZ(N, up, u), 1, 1)


def certB4(N, u, up):
    return edge4_keys(*famZ(N, up, u), 2, 1)


def certB1(N, u, up):
    return edge1_keys(*famZ(N, up, u), 2, 1)


def ok(keys):
    return all(v >= 0 for _, v in keys)


def regD(N, u, up):
    M = N + 2
    r = u % 2
    if u < 4 or up < u or u + up > N:
        return False
    if (u - r) * M * (u + up + 1) < 2 * (u + 1) * (M * u + 2 * u * up + u):
        return False
    if (u * M - r * M - 2 * u + 2) * (up + 1) < 2 * u * (up * up + M):
        return False
    return True


def regB(N, u, up):
    M = N + 2
    n = M - 2 * up
    c = u // 2
    if u < 3 or n < 3:
        return False
    if (u + 1) * (n - 1) > c * M:
        return False
    if u * (u + 1) > c * M:
        return False
    if c * M * (n + 2 * u) < u * ((2 * u + 1) * n - 2 * u) + u * (u + 1) * (2 * n + M - 1):
        return False
    if 2 * (u + 1) > c * up:
        return False
    return True
