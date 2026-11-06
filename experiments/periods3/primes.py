"""primes.py MMAX: which prime powers of B(m) are carried by the TOP components.

B(m) = lcm(2^(m-1), 2^a (2^s - 1) : a + s = m - 1).  Odd part = lcm_{s <= m-1} (2^s - 1), so
v_p(B(m)) = max_{s <= m-1} v_p(2^s - 1) = v_p(2^o - 1) + max{ j : o p^j <= m - 1 } (LTE, o = ord_p 2).
The order-(2^(m-1) - 1) component carries the full p-part iff v_p(2^(m-1) - 1) = v_p(B(m)), i.e.
iff o p^J divides m - 1 (J the maximal j).  Otherwise the p-part needs a component of an order
2^a (2^s - 1) with s < m - 1 (an s-cycle face, s in S_p = the s <= m-1 attaining the max).
"""
import sys
from sympy import factorint


def vp(x, p):
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 30
for m in range(3, MMAX + 1):
    odd = 1
    from math import lcm
    for s in range(1, m):
        odd = lcm(odd, 2 ** s - 1)
    fac = factorint(odd)
    top = 2 ** (m - 1) - 1
    cov, unc = [], []
    for p, v in sorted(fac.items()):
        S = [s for s in range(1, m) if vp(2 ** s - 1, p) == v]
        if (m - 1) in S:
            cov.append(f'{p}^{v}' if v > 1 else f'{p}')
        else:
            smax = max(S)
            unc.append((f'{p}^{v}' if v > 1 else f'{p}') + f'(s={smax})')
    print(f'm={m:2d}  top 2^(m-1)-1 carries: {" ".join(cov) or "-"}   needs s<m-1: {" ".join(unc) or "-"}')
