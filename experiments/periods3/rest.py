"""rest.py NMAX: the dominance ratios used in PROOFS.txt section 3.

Orbit (D = 2^n - 1):  M(l) = prod_{j<n} 1/(2|sin(pi 2^j l/D)|) * 1/(2|sin(pi l/D)|),
   R(n)  = sum_{l in (Z/D)^*, l not in +-<2>} M(l)/M(1).
Chain (2^n):          Mc(l) = prod_{j<n} 1/(2|sin(pi 2^j l/2^n)|) * 1/(2|sin(pi l/2^n)|),
   Rc(n) = sum_{l odd, l != +-1 mod 2^n} Mc(l)/Mc(1).
Numerically for n <= NMAX (numpy, float64, log-sums), and the rigorous analytic upper bounds
   R(n)  <= Bo(n) = sum_{lam odd, 3 <= lam < 2^9} (pi/2)^(n+1) 4^b lam^-(n-b) 2 (2/lam + 2^(b+2)/D)
                    + D (pi/2)^(n+1) 2^(-3n)                 (b = bit length of lam)
   Rc(n) <= Bc(n) = 2 G (pi/2) sum_{lam odd, 3 <= lam < 2^(n-1)} lam^-(n-b+1),  G = 1.809..
(derivations in PROOFS.txt 3.3), evaluated for n = 20..60 (both bounds decrease in n).
"""
import sys
import numpy as np
from math import gcd, pi, log, exp


def orbit_R(n):
    D = 2 ** n - 1
    l = np.arange(1, D, dtype=np.int64)
    good = np.gcd(l, D) == 1
    orb = set()
    for j in range(n):
        orb.add(pow(2, j, D))
        orb.add(D - pow(2, j, D))
    tot = 0.0
    L1 = None
    CH = 1 << 21
    for s in range(0, len(l), CH):
        ll = l[s:s + CH]
        g = good[s:s + CH]
        lm = -np.log(2 * np.abs(np.sin(np.pi * ll / D)))
        c = ll.copy()
        for j in range(n):
            lm -= np.log(2 * np.abs(np.sin(np.pi * c / D)))
            c = (2 * c) % D
        if s == 0:
            L1 = lm[0]
        mask = g & ~np.isin(ll, list(orb))
        tot += np.exp(lm[mask] - L1).sum()
    return tot


def chain_R(n):
    P = 2 ** n
    l = np.arange(1, P, 2, dtype=np.int64)
    lm = -np.log(2 * np.abs(np.sin(np.pi * l / P)))
    c = l.copy()
    for j in range(n):
        lm -= np.log(2 * np.abs(np.sin(np.pi * c / P)))
        c = (2 * c) % P
    L1 = lm[0]
    mask = (l != 1) & (l != P - 1)
    return np.exp(lm[mask] - L1).sum()


def Bo(n):
    D = 2 ** n - 1
    s = 0.0
    for lam in range(3, 2 ** 9, 2):
        b = lam.bit_length()
        s += exp((n + 1) * log(pi / 2) + b * log(4) - (n - b) * log(lam)) * 2 * (2 / lam + 2 ** (b + 2) / D)
    s += exp(n * log(2) + (n + 1) * log(pi / 2) - 3 * n * log(2))
    return s


def Bc(n):
    """2 G (pi/2) sum_{lam odd, 3 <= lam < 2^(n-1)} lam^-(n-b+1), G = prod_k (pi/2^k)/sin(pi/2^k)."""
    from math import sin
    G = 1.0
    for k in range(1, 80):
        G *= (pi / 2 ** k) / sin(pi / 2 ** k)
    s = 0.0
    top = min(2 ** (n - 1), 2 ** 20)
    for lam in range(3, top, 2):
        b = lam.bit_length()
        s += exp(-(n - b + 1) * log(lam))
    for b in range(21, n):
        # odd lam in [2^(b-1), 2^b): 2^(b-2) values, each <= 2^-((b-1)(n-b+1))
        s += 2 ** (b - 2) * 2.0 ** (-(b - 1) * (n - b + 1))
    return 2 * G * (pi / 2) * s


if __name__ == '__main__':
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    print(' n   R(n) numeric    Rc(n) numeric')
    for n in range(3, NMAX + 1):
        r = orbit_R(n)
        rc = chain_R(n)
        print(f'{n:2d}   {r:.4e}      {rc:.4e}', flush=True)
    print(' n   Bo(n) (bound on R)   Bc(n) (bound on Rc)')
    for n in list(range(16, 31)) + [40, 50, 60]:
        print(f'{n:2d}   {Bo(n):.4e}           {Bc(n):.4e}', flush=True)
