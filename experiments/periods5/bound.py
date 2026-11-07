"""bound.py: the explicit upper bound U(s,a) >= rest2(s,a) (PROOFS.txt sections 2-5), float
prototype.  U = U_alpha + U_I + U_II."""
import sys
import math
from math import comb, sin, tan, pi, log, floor

G = 1.0
for _k in range(1, 80):
    _x = 2.0 ** -_k
    G *= pi * _x / sin(pi * _x)


def gam(y):
    return 1.0 if y == 0 else pi * y / sin(pi * y)


def U_alpha(s, a, debug=False):
    """u = +-1 mod D, u != +-1, j = 0; sum over e* (Lemma 3), tower recursion B."""
    D = 2 ** s - 1
    q = 2 ** a * D
    C0 = comb(s + a, a)
    Q = [q // 2 ** e for e in range(a + 1)]          # Q[a] = D
    memo = {}

    def rb(e, tau):          # bound for rho at position e with sym residue >= tau mod Q[e]
        if e > s:
            return 1.0
        return min(1.0, sin(pi / Q[e]) / sin(pi * tau / Q[e]))

    def B(e, tau):
        if e == 0:
            return 1.0
        key = (e, tau)
        if key not in memo:
            memo[key] = rb(e - 1, tau) * B(e - 1, tau) + rb(e - 1, Q[e] / 2) * B(e - 1, Q[e] / 2)
        return memo[key]

    tot = 0.0
    for es in range(min(a, s)):
        if es == a - 1:
            continue                 # u = +-1 mod D, u != +-1 mod 2D: u even
        ch = 1.0
        L = a - es
        for l in range(max(L, 2), a + 1):
            if l == L:
                ch *= tan(pi / 2 ** l)
            else:
                lam = 2 ** (L - 1) - 1
                if lam >= 1:
                    ch *= min(1.0, sin(pi / 2 ** l) / sin(pi * lam / 2 ** l))
        cy = tan(pi / Q[es]) if es <= s else 1.0
        cy *= B(es, Q[es + 1] - 1)
        tot += 2 * C0 * ch * cy
        if debug:
            print(f'   e*={es}: {2 * C0 * ch * cy:.3g}  (chain {ch:.3g}, cycle {cy:.3g})')
    return tot


def kappa(s, q, j):
    return sin(pi * 2 ** s / q) / sin(pi * 2 ** (s - j) / q)


def chainA(d, a):
    p = 1.0
    for l in range(1, a + 1):
        m = d % 2 ** l
        m = min(m, 2 ** l - m)
        p *= sin(pi / 2 ** l) / sin(pi * m / 2 ** l)
    return p


def U_I(s, a, T=4000):
    """no fold in [0, s-1]: u = +-d, d odd, 3 <= d <= q/2^(s+1), d != +-1 mod D."""
    D = 2 ** s - 1
    q = 2 ** a * D
    dmax = q // 2 ** (s + 1)
    W = [comb(s - j + a, a) * kappa(s, q, j) for j in range(s)]
    tot = 0.0
    d = 3
    while d <= min(dmax, T):
        if math.gcd(d, D) == 1:
            cyc = 1.0
            for e in range(s):
                cyc *= sin(pi * 2 ** e / q) / sin(pi * 2 ** e * d / q)
            eq = sum(W[j] * sin(pi * 2 ** s / q) / kappa(s, q, j) / sin(pi * 2 ** (s - j) * d / q)
                     for j in range(s))
            tot += 2 * chainA(d, a) * cyc * eq
        d += 2
    if dmax > T:
        # tail: R <= G^2 gam(2^-j-1) d^-(s+1) * G d^-(a-b) * kappa_j
        Weq = sum(W[j] * gam(2.0 ** (-j - 1)) for j in range(s))
        b0 = T.bit_length()
        for b in range(b0, a):
            lo = max(T + 1, 2 ** (b - 1))
            hi = min(dmax, 2 ** b - 1)
            if lo > hi:
                continue
            cnt = (hi - lo) // 2 + 1
            tot += 2 * cnt * G ** 2 * Weq * lo ** (-(s + 1 + a - b))
    return tot


def U_II(s, a, debug=False):
    D = 2 ** s - 1
    q = 2 ** a * D

    def dmin(p, g):
        """smallest admissible d_p > q 2^(p-g-2)."""
        lo = q * 2.0 ** (p - g - 2)
        if p == 0:
            d = max(3, floor(lo) + 1)
            if d % 2 == 0:
                d += 1
            return d
        if p < a:
            t = max(3, floor(lo / 2 ** p) + 1)
            if t % 2 == 0:
                t += 1
            return t * 2 ** p
        t = max(2 if p == a else 1, floor(lo / 2 ** a) + 1)
        return t * 2 ** a

    def pimax(p, g):
        return 2 ** p / dmin(p, g)

    def dmax(p, g):
        """largest admissible d_p <= q 2^(p-g-1) (closed run [p, g]: y_g <= 1/2)."""
        hi = q * 2 ** p // 2 ** (g + 1) if g + 1 <= 62 else floor(q * 2.0 ** (p - g - 1))
        if p == 0:
            return hi if hi % 2 == 1 else hi - 1
        if p < a:
            t = hi // 2 ** p
            if t % 2 == 0:
                t -= 1
            return t * 2 ** p
        return (hi // 2 ** a) * 2 ** a

    def S(n, p, clo=0):
        """sup over admissible APs (difference 2^(p+1), elements >= clo, <= X) of sum (2^p/d)^n."""
        X = q * 2.0 ** (p - s - 1)
        if p < a:
            t0 = max(3, -(-clo // 2 ** p))
            if t0 % 2 == 0:
                t0 += 1
            Tm = X / 2 ** p          # t odd, t0 <= t <= Tm
            if Tm < t0:
                return 0.0
            if n == 0:
                return floor((Tm - t0) / 2) + 1
            if n == 1:
                return 1 / t0 + log(Tm / t0) / 2
            return t0 ** -n + t0 ** (1 - n) / (2 * (n - 1))
        c = max(2 ** a * (2 if p == a else 1), -(-clo // 2 ** a) * 2 ** a)
        if c > X:
            return 0.0
        N = floor((X - c) / 2 ** (p + 1)) + 1
        first = (2 ** p / c) ** n
        if n == 0:
            return N
        if n == 1:
            rest = 0.0 if N <= 1 else 0.5 * (1 + log(N - 1))
            return first + rest
        z = sum((2 * i) ** (-n) for i in range(1, 200)) + (2 * 200) ** (1 - n) / (2 * (n - 1))
        return first + z

    Cj = {e: comb(e + a, a) * kappa(s, q, s - e) for e in range(1, s + 1)}   # eq position e = s - j

    def Gam(e, g):
        return gam(2.0 ** (e - g - 1))

    def E(p, g):
        return sum(Cj[e] * Gam(e, g) for e in range(max(p, 1), g + 1))

    def P(p, g, gn):
        """bound for P on the closed run [p, g] whose next run ends at gn (gn = s: last run)."""
        return min(2 ** p / dmin(p, g), 2 ** (g + 1) / (q * (1 - 2.0 ** (g - gn))))

    # DP over (previous fold gp, current fold g); gp = -1 for the first run.
    DP0 = {}
    DP1 = {}
    for g in range(s):
        DP0[(-1, g)] = 1.0
        DP1[(-1, g)] = 0.0
    tot = 0.0
    contrib = [0.0] * s
    for g in range(s):
        for gp in range(-1, g):
            v0, v1 = DP0[(gp, g)], DP1[(gp, g)]
            if v0 == 0 and v1 == 0:
                continue
            ell = g - gp
            Ec = E(gp + 1, g)
            for gn in range(g + 1, s + 1):
                pp = P(gp + 1, g, gn)
                f = G * pp ** ell
                w0 = v0 * f
                w1 = v1 * f + v0 * f * Ec * pp
                if gn < s:
                    DP0[(g, gn)] = DP0.get((g, gn), 0.0) + w0
                    DP1[(g, gn)] = DP1.get((g, gn), 0.0) + w1
                else:
                    p = g + 1
                    n = s - p
                    clo = q - 2 ** (g - gp) * dmax(gp + 1, g)
                    c = w1 * S(n, p, clo) + w0 * E(p, s) * S(n + 1, p, clo)
                    tot += c
                    contrib[g] += c
    if debug:
        for g in range(s):
            print(f'   last fold g={g}: {2 * G * contrib[g]:.3g}')
    return 2 * G * tot


if __name__ == '__main__':
    s, a = int(sys.argv[1]), int(sys.argv[2])
    print(s, a, f'alpha {U_alpha(s, a):.4g}  I {U_I(s, a):.4g}  II {U_II(s, a):.4g}')
