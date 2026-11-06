"""slicelib.py: exact slice constraints (Lean `sliceCons` / `sliceCons'`) and the feasible window
of the bottom height c0 for the direction w1 = (1, 0) (corners (s0, c0), (s0 + 1, c0), (s1, c0 + 1),
(s1 + 1, c0 + 1)).  Option = (o, f, t, p, j): orientation o (1: (x, y) = (u', u)), family f
(0 Z, 1 X0, 2 X1), slice t (0: a = p c + j in (s, c); 1: c = p a + j in (s, a))."""
from fractions import Fraction as F


def family(N, y, f):
    """(K, R, al, be, smax, amin) of family f with right index y."""
    if f == 0:
        return N + 2, y, 0, 1, (N + 2) // 2, 2
    if f == 1:
        return N, y - 2, 0, 1, (N + 1) // 2, 1
    return N, y - 2, 1, 0, N // 2, 2


def smax_lb(N, f):
    """the lower bound of smax used in Lean (rational)."""
    return F(N + 1, 2) if f == 0 else (F(N, 2) if f == 1 else F(N - 1, 2))


def cons(N, u, v, opt, exact_smax=True):
    """the 8 forms (A, C, D): A s + C c + D >= 0 (c is the second slice variable)."""
    o, f, t, p, j = opt
    x, y = (v, u) if o == 1 else (u, v)
    K, R, al, be, smax, amin = family(N, y, f)
    L = x
    S = smax if exact_smax else smax_lb(N, f)
    if t == 0:
        return [(-L, p * K, j * K - al), (L + 1, -p * K, al - 1 - j * K), (-R, K, -be), (R + 1, -K, be - 1),
                (1, 0, -2), (1, 0, -R), (-1, 0, S), (0, p, j - amin)]
    return [(-L, K, -al), (L + 1, -K, al - 1), (-R, p * K, j * K - be), (R + 1, -p * K, be - 1 - j * K),
            (1, 0, -2), (1, 0, -R), (-1, 0, S), (0, 1, -amin)]


def window(cs):
    """the interval [lo, hi] of c0 such that the chords at c0 and c0 + 1 have length >= 1, or None."""
    lows = [(A, C, D) for A, C, D in cs if A > 0]    # s >= -(C c + D)/A
    ups = [(A, C, D) for A, C, D in cs if A < 0]     # s <= (C c + D)/(-A)
    flat = [(A, C, D) for A, C, D in cs if A == 0]
    lo, hi = None, None

    def add(e, f_):  # e c >= f_
        nonlocal lo, hi
        if e == 0:
            if f_ > 0:
                lo, hi = F(1), F(0)
            return
        b = F(f_, 1) / e
        if e > 0:
            lo = b if lo is None or b > lo else lo
        else:
            hi = b if hi is None or b < hi else hi
    for A, C, D in flat:
        add(C, -D)
    for Al, Cl, Dl in lows:
        for Au, Cu, Du in ups:
            # (Cu c + Du)/(-Au) + (Cl c + Dl)/Al >= 1
            # Al (Cu c + Du) + (-Au)(Cl c + Dl) >= Al (-Au)
            e = Al * Cu + (-Au) * Cl
            add(e, Al * (-Au) - Al * Du - (-Au) * Dl)
    if lo is None or hi is None:
        return None
    return lo, hi - 1  # c0 in [lo, hi - 1] (c0 + 1 also in [lo, hi])


def maxlow(cs, c):
    best, arg = None, None
    for i, (A, C, D) in enumerate(cs):
        if A > 0:
            val = -(F(C) * c + D) / A
            if best is None or val > best:
                best, arg = val, i
    return best, arg


def window_arg(cs):
    """as window, also returning the binding constraints (pairs (lower, upper) or ('flat', i))."""
    lows = [(i, f) for i, f in enumerate(cs) if f[0] > 0]
    ups = [(i, f) for i, f in enumerate(cs) if f[0] < 0]
    flat = [(i, f) for i, f in enumerate(cs) if f[0] == 0]
    lo = hi = None
    alo = ahi = None
    cands = []
    for i, (A, C, D) in flat:
        cands.append((C, -D, ('flat', i)))
    for il, (Al, Cl, Dl) in lows:
        for iu, (Au, Cu, Du) in ups:
            cands.append((Al * Cu + (-Au) * Cl, Al * (-Au) - Al * Du - (-Au) * Dl, (il, iu)))
    for e, f_, tag in cands:
        if e == 0:
            if f_ > 0:
                return None
            continue
        b = F(f_) / e
        if e > 0:
            if lo is None or b > lo:
                lo, alo = b, tag
        else:
            if hi is None or b < hi:
                hi, ahi = b, tag
    if lo is None or hi is None:
        return None
    return lo, hi - 1, alo, ahi
