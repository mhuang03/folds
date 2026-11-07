"""split.py S A: the exact rest2(s, a) of ../periods4 (float64, all units), split into
   alpha : u = +-1 mod D, u != +-1, j = 0   (j >= 1 is excluded by the rotation lemma)
   I     : u != +-1 mod D, no fold in [0, s-1]   (|u| <= q/2^(s+1))
   II    : u != +-1 mod D, some fold in [0, s-1]
(fold at e:  ||2^e u/q|| > 1/4)."""
import sys
import numpy as np
from math import comb


def logfac(x):
    return -np.log(2 * np.abs(np.sin(np.pi * x)))


def split(s, a, block=1 << 22):
    D = 2 ** s - 1
    q = 2 ** a * D
    cs = [D * 2 ** (i - 1) for i in range(1, a + 1)] + [2 ** e for e in range(s)]
    L0 = sum(logfac(c / q) for c in cs) + logfac(2 ** s / q)
    out = {'alpha': 0.0, 'I': 0.0, 'II': 0.0}
    for start in range(1, q, block):
        u = np.arange(start, min(start + block, q), dtype=np.int64)
        u = u[(u % 2 == 1) & (np.gcd(u, D) == 1)]
        u = u[(u != 1) & (u != q - 1)]
        rot = ((u % D) == 1) | ((u % D) == D - 1)
        d0 = np.minimum(u, q - u)
        nofold = d0 * 2 ** (s - 1) * 4 <= q
        L = np.zeros(len(u))
        for c in cs:
            L += logfac(((u * c) % q) / q)
        for j in range(s):
            r = np.exp(L + logfac(((u * 2 ** (s - j)) % q) / q) - L0) * comb(s - j + a, a)
            if j == 0:
                out['alpha'] += float(r[rot].sum())
            out['I'] += float(r[~rot & nofold].sum())
            out['II'] += float(r[~rot & ~nofold].sum())
    return out


if __name__ == '__main__':
    s, a = int(sys.argv[1]), int(sys.argv[2])
    o = split(s, a)
    print(s, a, {k: f'{v:.4g}' for k, v in o.items()}, f'total {sum(o.values()):.4g}')
