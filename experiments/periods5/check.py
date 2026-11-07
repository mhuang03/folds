"""check.py KMIN KMAX: brute-force sanity check of the class bounds of PROOFS.txt.
For every s >= 4, a >= 2 with KMIN <= s+a+1 <= KMAX, all units u mod q are classified
   alpha : u = +-1 mod q/2^n (n = min(a, s)), u != +-1         -> j = 0 only
   I     : not alpha, no fold in [0, s-1]
   0     : not alpha, fold set in [0, s-1] equal to {0}
   II'   : not alpha, some fold in [1, s-1]
and the exact class sums of C(s-j+a, a) M(u,j)/M(1,0) (float64) are compared with
Ua, UI, U0, Vp of ubound.py.  Also checks rest2 (periods4 definition) <= total."""
import sys
import numpy as np
from math import comb
from ubound import Ua, UI, U0, Vp


def logfac(x):
    return -np.log(2 * np.abs(np.sin(np.pi * x)))


def classes(s, a):
    D = 2 ** s - 1
    q = 2 ** a * D
    n = min(a, s)
    Qn = q // 2 ** n
    cs = [D * 2 ** (i - 1) for i in range(1, a + 1)] + [2 ** e for e in range(s)]
    L0 = sum(logfac(c / q) for c in cs) + logfac(2 ** s / q)
    u = np.arange(1, q, dtype=np.int64)
    u = u[(u % 2 == 1) & (np.gcd(u, D) == 1)]
    u = u[(u != 1) & (u != q - 1)]
    alpha = ((u % Qn) == 1) | ((u % Qn) == Qn - 1)
    rot = ((u % D) == 1) | ((u % D) == D - 1)
    folds = np.zeros((s, len(u)), bool)
    for e in range(s):
        x = (u * 2 ** e) % q
        d = np.minimum(x, q - x)
        folds[e] = 4 * d > q
    nofold = ~folds.any(axis=0)
    only0 = folds[0] & ~folds[1:].any(axis=0)
    other = folds[1:].any(axis=0)
    L = np.zeros(len(u))
    for c in cs:
        L += logfac(((u * c) % q) / q)
    out = dict(alpha=0.0, I=0.0, Z=0.0, II=0.0, rest2=0.0)
    for j in range(s):
        r = np.exp(L + logfac(((u * 2 ** (s - j)) % q) / q) - L0) * comb(s - j + a, a)
        if j == 0:
            out['alpha'] += float(r[alpha].sum())
            out['rest2'] += float(r.sum())
        else:
            out['rest2'] += float(r[~rot].sum())
        out['I'] += float(r[~alpha & nofold].sum())
        out['Z'] += float(r[~alpha & only0].sum())
        out['II'] += float(r[~alpha & other].sum())
    return out


if __name__ == '__main__':
    k0, k1 = int(sys.argv[1]), int(sys.argv[2])
    worst = {}
    for k in range(k0, k1 + 1):
        for s in range(4, k - 2):
            a = k - 1 - s
            o = classes(s, a)
            b = dict(alpha=float(Ua(s, a).upper()), I=float(UI(s, a).upper()),
                     Z=float(U0(s, a).upper()), II=float(Vp(s, a).upper()))
            tot = sum(b.values())
            ok = all(o[c] <= b[c] * (1 + 1e-9) + 1e-300 for c in b) and o['rest2'] <= tot
            ratios = {c: (o[c] / b[c] if b[c] > 0 else (0 if o[c] == 0 else float('inf'))) for c in b}
            for c, v in ratios.items():
                worst[c] = max(worst.get(c, 0), v)
            print(f'k={k} (s,a)=({s},{a}) {"OK " if ok else "FAIL"} rest2={o["rest2"]:.3g} '
                  f'bound={tot:.3g}  true/bound: ' + ' '.join(f'{c}={v:.2g}' for c, v in ratios.items()),
                  flush=True)
    print('max true/bound per class:', {c: f'{v:.3g}' for c, v in worst.items()})
