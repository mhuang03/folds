"""dominance.py NMAX: size of the orbit-vertex terms at the Fourier mode e(-N/D), D = 2^n - 1.

A valid orbit vertex with x_1 = a/D contributes to the coefficient of e(N r/D) in c_0 a single
monomial of modulus M(l)/D, l = r a^{-1} mod D (when gcd(a, D) = 1), where
   M(l) = prod_{i=0}^{n-1} 1/(2|sin(pi 2^i l/D)|) * 1/(2|sin(pi l/D)|)
(PROOFS.txt section 2).  For r = 1 the vertex a = 1 gives M(1).  We compare
   rest(n) = sum over ALL l in (Z/D)^* outside {+-2^i} of M(l)       (no validity used)
   rot(n)  = sum over l = +-2^i, i >= 1 of M(l)
with M(1), and the term of the other valid vertex a = 3 (l = 3^{-1}) when gcd(3, D) = 1.
"""
import sys
from math import sin, pi, log, gcd


def logM(l, n, D):
    s = 0.0
    for i in range(n):
        s -= log(2 * abs(sin(pi * ((pow(2, i, D) * l) % D) / D)))
    return s - log(2 * abs(sin(pi * l / D)))


if __name__ == '__main__':
    NMAX = int(sys.argv[1])
    print(' n      D   log10 M(1)   rest/M(1)     rot/M(1)   M(3^-1)/M(1)')
    for n in range(3, NMAX + 1):
        D = 2 ** n - 1
        L1 = logM(1, n, D)
        orb = {pow(2, i, D) for i in range(n)} | {D - pow(2, i, D) for i in range(n)}
        rest = 0.0
        rot = 0.0
        for l in range(1, D):
            if gcd(l, D) != 1:
                continue
            if l in (1, D - 1):
                continue
            r = 2.718281828459045 ** (logM(l, n, D) - L1)
            if l in orb:
                rot += r
            else:
                rest += r
        t3 = '-'
        if gcd(3, D) == 1:
            l3 = pow(3, -1, D)
            t3 = f'{2.718281828459045 ** (logM(l3, n, D) - L1):.3e}'
        print(f'{n:2d} {D:7d} {L1 / log(10):11.3f}   {rest:.3e}   {rot:.3e}   {t3}', flush=True)
