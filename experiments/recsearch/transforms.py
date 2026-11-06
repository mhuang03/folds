"""Exact transforms of a sequence s[1..L] (Python list with s[0] = None or a value)."""
from fractions import Fraction
from math import factorial, comb
from functools import lru_cache


def ser(s, s0=1):
    """OGF coefficient list g[0..L] with g[0] = s0."""
    return [Fraction(s0)] + [Fraction(x) for x in s[1:]]


def s_exp(g):          # exp of a series with g[0] = 0
    L = len(g) - 1
    h = [Fraction(1)] + [Fraction(0)] * L
    for n in range(1, L + 1):
        h[n] = Fraction(sum((k * g[k] * h[n - k] for k in range(1, n + 1)), Fraction(0)), n)
    return h


def s_log(g):          # log of a series with g[0] = 1
    L = len(g) - 1
    f = [Fraction(0)] * (L + 1)
    for n in range(1, L + 1):
        f[n] = g[n] - Fraction(sum((k * f[k] * g[n - k] for k in range(1, n)), Fraction(0)), n)
    return f


def s_inv(g):          # 1/g, g[0] = 1
    L = len(g) - 1
    h = [Fraction(1)] + [Fraction(0)] * L
    for n in range(1, L + 1):
        h[n] = -sum(g[k] * h[n - k] for k in range(1, n + 1))
    return h


def ogf_log(s):
    return [None] + s_log(ser(s, 1))[1:]


def ogf_exp(s):
    return [None] + s_exp(ser(s, 0))[1:]


def ogf_inv(s):
    return [None] + s_inv(ser(s, 1))[1:]


def to_egf(s, s0):
    g = ser(s, s0)
    return [x / factorial(n) for n, x in enumerate(g)]


def from_egf(h):
    return [None] + [x * factorial(n) for n, x in enumerate(h)][1:]


def egf_log(s):
    return from_egf(s_log(to_egf(s, 1)))


def egf_exp(s):
    return from_egf(s_exp(to_egf(s, 0)))


def egf_inv(s):
    return from_egf(s_inv(to_egf(s, 1)))


def binomial(s, s0=0):
    g = ser(s, s0)
    return [None] + [sum(comb(n, k) * g[k] for k in range(n + 1)) for n in range(1, len(g))]


def inv_binomial(s, s0=0):
    g = ser(s, s0)
    return [None] + [sum((-1) ** (n - k) * comb(n, k) * g[k] for k in range(n + 1)) for n in range(1, len(g))]


def over_fact(s):
    return [None] + [Fraction(x, factorial(n)) for n, x in enumerate(s) if n >= 1]


# --- OEIS-style transforms (Sloane's "transforms" page conventions) ---------------
def mobius(n):
    m, p, res = n, 2, 1
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    if m > 1:
        res = -res
    return res


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def euler(s):
    """b with prod_n (1-x^n)^(-s_n) = 1 + sum b_n x^n."""
    L = len(s) - 1
    c = [0] + [sum(d * s[d] for d in divisors(n)) for n in range(1, L + 1)]
    b = [Fraction(1)] + [Fraction(0)] * L
    for n in range(1, L + 1):
        b[n] = Fraction(c[n] + sum(c[k] * b[n - k] for k in range(1, n)), n)
    return [None] + b[1:]


def inv_euler(b):
    L = len(b) - 1
    bb = [1] + list(b[1:])
    c = [0] * (L + 1)
    for n in range(1, L + 1):
        c[n] = n * bb[n] - sum(c[k] * bb[n - k] for k in range(1, n))
    return [None] + [Fraction(sum(mobius(n // d) * c[d] for d in divisors(n)), n) for n in range(1, L + 1)]


def mobius_tr(s):
    L = len(s) - 1
    return [None] + [sum(mobius(n // d) * s[d] for d in divisors(n)) for n in range(1, L + 1)]


def stirling2_tr(s):
    """b_n = sum_k S(n,k) s_k."""
    L = len(s) - 1
    S = [[0] * (L + 1) for _ in range(L + 1)]
    S[0][0] = 1
    for n in range(1, L + 1):
        for k in range(1, n + 1):
            S[n][k] = k * S[n - 1][k] + S[n - 1][k - 1]
    return [None] + [sum(S[n][k] * s[k] for k in range(1, n + 1)) for n in range(1, L + 1)]


def stirling1_tr(s):
    """b_n = sum_k s(n,k) s_k with signed Stirling numbers of the first kind."""
    L = len(s) - 1
    S = [[0] * (L + 1) for _ in range(L + 1)]
    S[0][0] = 1
    for n in range(1, L + 1):
        for k in range(1, n + 1):
            S[n][k] = S[n - 1][k - 1] - (n - 1) * S[n - 1][k]
    return [None] + [sum(S[n][k] * s[k] for k in range(1, n + 1)) for n in range(1, L + 1)]


def boustrophedon(s, s0=1):
    """Boustrophedon transform of (s0, s1, ..., sL), indices shifted so b[n] uses s[0..n]."""
    g = [s0] + list(s[1:])
    L = len(g) - 1
    out = [g[0]]
    row = [g[0]]
    for n in range(1, L + 1):
        new = [g[n]]
        for k in range(1, n + 1):
            new.append(new[-1] + row[n - k])
        row = new
        out.append(row[-1])
    return [None] + out[1:]


def invert(s):
    """1 + sum b x^n = 1/(1 - sum s x^n)."""
    g = [Fraction(0)] + [Fraction(-x) for x in s[1:]]
    g[0] = Fraction(1)
    return [None] + s_inv(g)[1:]


def inv_invert(b):
    """s with 1/(1 - sum s x^n) = 1 + sum b x^n, i.e. s = 1 - 1/(1+B)."""
    h = s_inv(ser(b, 1))
    return [None] + [-x for x in h[1:]]
