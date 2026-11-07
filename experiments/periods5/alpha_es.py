"""alpha_es.py S A: exact class-alpha terms (u = +-1 mod D, u != +-1, j = 0) grouped by e*
(largest e with u != +-1 mod q/2^e), against the per-e* bound of bound.U_alpha (exploration)."""
import sys
import numpy as np
from math import comb

s, a = int(sys.argv[1]), int(sys.argv[2])
D = 2 ** s - 1
q = 2 ** a * D
C0 = comb(s + a, a)


def lf(x):
    return -np.log(2 * np.abs(np.sin(np.pi * x)))


cs = [D * 2 ** (i - 1) for i in range(1, a + 1)] + [2 ** e for e in range(s)] + [2 ** s]
L0 = sum(lf(c / q) for c in cs)
tot = {}
for sg in (1, -1):
    for c in range(2 ** a):
        u = (sg + D * c) % q
        if u % 2 == 0 or u in (1, q - 1):
            continue
        es = max(e for e in range(a + 1) if (u % (q // 2 ** e)) not in (1, q // 2 ** e - 1))
        r = np.exp(sum(lf((u * cc % q) / q) for cc in cs) - L0) * C0
        tot[es] = tot.get(es, 0) + r
print({k: f'{v:.3g}' for k, v in sorted(tot.items())})
