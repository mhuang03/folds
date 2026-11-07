"""ubound.py: the explicit majorant of rest2(s, a) of PROOFS.txt, in ball arithmetic (python-flint arb).

   rest2(s, a) <= U(s, a) = Ua(s, a) + UI(s, a) + U0(s, a) + Vp(s, a)        (Theorem 5.1)

   Ua  class alpha (u = +-1 mod q/2^n, n = min(a, s), u != +-1), Lemma 3.1
   UI  class I     (no fold in [0, s-1]), Lemma 4.1 (closed form f_I)
   U0  class 0     (fold pattern {0}), Lemma 4.2
   Vp  class II'   (fold pattern with a fold in [1, s-1]), Lemma 4.4 / Proposition 4.5
All functions return arb balls; every inequality used is an upper bound, so the upper end of the
ball is a rigorous upper bound for the quantity in PROOFS.txt."""
from math import comb
from flint import arb, ctx

ctx.prec = 128
PI = arb.pi()
TWO = arb(2)


def gam(y):
    """gamma(y) = pi y / sin(pi y)."""
    y = arb(y)
    return PI * y / (PI * y).sin()


def _G(start):
    p = arb(1)
    for i in range(start, 200):
        p *= gam(TWO ** -i)
    # tail prod_{i>=200} gamma(2^-i) <= exp(sum (pi 2^-i)^2/5) < 1 + 2^-390
    return p * (1 + TWO ** -390)


G = _G(1)            # prod_{i>=1} gamma(2^-i)  = 1.80579...
G2 = _G(2)           # prod_{i>=2} gamma(2^-i)  = G / (pi/2)
K = G / (1 - G / 2)  # Lemma 4.3


def eps_(s):
    return 1 / (1 - TWO ** -s)


# ---------------------------------------------------------------- class alpha (Lemma 3.1)
def Ua(s, a):
    D = 2 ** s - 1
    q = 2 ** a * D
    C = comb(s + a, a)
    tot = (PI / TWO ** a).tan() * (PI / q).tan()
    for es in range(1, min(a - 2, s - 1) + 1):
        Qn = q // 2 ** (es + 1)
        tot += (TWO ** es * (PI / TWO ** (a - es)).tan() * (PI * TWO ** es / q).tan()
                * (PI / (2 * (Qn - 1))) ** es)
    return 2 * C * tot


# ---------------------------------------------------------------- class I (Lemma 4.1)
def UI(s, a):
    k = s + a + 1
    return PI * G * G2 * (9 * (TWO / 3) ** k + 128 * k * TWO ** -k)


# ---------------------------------------------------------------- class 0 (Lemma 4.2)
def U0(s, a):
    m = s + a
    if a == 2:
        return arb(0)          # no odd t with 3 <= t <= q/2^(s+1) < 2
    eps = eps_(s)
    cos0 = (PI / TWO ** (s + 1)).cos()
    pref = 2 * PI ** 2 * eps * G2 / cos0
    inner = (G * TWO.sqrt() * PI * TWO ** -a * (27 * arb(3) ** -m + m * TWO ** (9 - 2 * m))
             + arb(3) ** (3 - m) + TWO ** (9 - 2 * m))
    return pref * inner


# ---------------------------------------------------------------- class II' (Prop. 4.5)
def S(n, p, s, a):
    """Lemma 4.4: sum over the last-run values d_p of (2^p/d)^n."""
    q = 2 ** a * (2 ** s - 1)
    # X = q 2^(p-s-1);  all comparisons on exact integers / rationals
    if p < a:
        T = q // 2 ** (s + 1)            # t odd, 3 <= t <= q/2^(s+1)  (q/2^(s+1) is an integer here)
        if T < 3:
            return arb(0)
        if n == 0:
            return arb((T - 1) // 2)
        if n == 1:
            return arb(1) / 3 + (arb(T) / 3).log() / 2
        return arb(3) ** -n + arb(3) ** (1 - n) / (2 * (n - 1))
    c = 2 ** a * (2 if p == a else 1)
    # X = q 2^(p-s-1) >= c ?   (2X = q 2^(p-s) is an integer when p >= s; else compare scaled)
    if q * 2 ** p < c * 2 ** (s + 1):
        return arb(0)
    N = (q * 2 ** p - c * 2 ** (s + 1)) // (2 ** (p + 1) * 2 ** (s + 1)) + 1
    first = (TWO ** p / c) ** n
    if n == 0:
        return arb(N)
    if n == 1:
        return first + (0 if N <= 1 else (1 + arb(N - 1).log()) / 2)
    return first + TWO ** -n * (1 + arb(1) / (n - 1))


def Vp(s, a, gmin=1):
    m = s + a
    eps = eps_(s)
    w = [arb(0)] + [comb(e + a, a) * TWO ** (s - e) for e in range(1, s + 1)]
    pre = [arb(0)] * (s + 2)
    for e in range(1, s + 1):
        pre[e] = pre[e - 1] + w[e]
    tot = arb(0)
    for g in range(gmin, s):
        if g <= s - 2:
            c = 4 * eps / 3 * TWO ** (g + 1 - m)
            th = arb(3) / 2
        else:
            c = eps * TWO ** (1 - a)
            th = arb(1)
        sig = arb(0)
        for gp in range(g):
            sig += (th * TWO ** (gp - g)) ** (gp + 1)
        third = arb(1) / 3
        cm = third if c > third else c      # both are upper bounds for min(1/3, c)
        Cl = G * cm ** (g + 1) + G * K * sig * c ** (g + 1)
        p = g + 1
        n = s - p
        Ale = pre[g]
        Agt = pre[s] - pre[g]
        tot += Cl * (c * Ale * S(n, p, s, a) + Agt * S(n + 1, p, s, a))
    return PI * G * tot


def U(s, a):
    return Ua(s, a) + UI(s, a) + U0(s, a) + Vp(s, a)


if __name__ == '__main__':
    import sys
    s, a = int(sys.argv[1]), int(sys.argv[2])
    for f in (Ua, UI, U0, Vp, U):
        print(f.__name__, f(s, a).str(5, radius=False))
