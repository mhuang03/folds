"""crude.py KMAX [KMIN]: the crude dominance test for the mixed components (s >= 4, a >= 2):
   rest(s,a) = sum_{u unit mod q, u != +-1} sum_{j=0}^{s-1} C(s-j+a, a) * ratio(u, j)
(ratio = M(u,j)/M(1,0), PROOFS.txt section 3; C(s-j+a, a) bounds the number of valid time
orders of a structure).  Dominance needs rest < 2.  float64, vectorised over u."""
import sys
import numpy as np
from math import comb


def logfac(x):
    return -np.log(2 * np.abs(np.sin(np.pi * x)))


def rest(s, a, block=1 << 22, weights=None):
    D = 2 ** s - 1
    q = 2 ** a * D
    c_chain = [D * 2 ** (i - 1) for i in range(1, a + 1)]
    c_cyc = [2 ** e for e in range(s)]
    L0 = sum(logfac(c / q) for c in c_chain + c_cyc) + logfac(2 ** s / q)
    tot = 0.0
    worst = (0, None)
    for start in range(1, q, block):
        u = np.arange(start, min(start + block, q), dtype=np.int64)
        u = u[(u % 2 == 1) & (np.gcd(u, D) == 1)]
        u = u[(u != 1) & (u != q - 1)]
        L = np.zeros(len(u))
        for c in c_chain + c_cyc:
            L += logfac(((u * c) % q) / q)
        for j in range(s):
            r = np.exp(L + logfac(((u * 2 ** (s - j)) % q) / q) - L0)
            wgt = comb(s - j + a, a) if weights is None else weights(s, a, j)
            tot += wgt * r.sum()
            i = int(np.argmax(r))
            if r[i] > worst[0]:
                worst = (float(r[i]), (int(u[i]), j))
    return tot, worst


if __name__ == '__main__':
    K = int(sys.argv[1])
    K0 = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    for k in range(K0, K + 1):
        for s in range(4, k - 2):
            a = k - 1 - s
            t, w = rest(s, a)
            print(f'k={k:2d} s={s:2d} a={a:2d}  crude rest = {t:.4g}   max ratio {w[0]:.3g} at (u,j)={w[1]}',
                  flush=True)


def rest2(s, a, block=1 << 22, top=0):
    """crude tail after the rotation lemma: exclude u = +-1 (all j) and u = +-1 mod D with j >= 1."""
    D = 2 ** s - 1
    q = 2 ** a * D
    c_chain = [D * 2 ** (i - 1) for i in range(1, a + 1)]
    c_cyc = [2 ** e for e in range(s)]
    L0 = sum(logfac(c / q) for c in c_chain + c_cyc) + logfac(2 ** s / q)
    tot = 0.0
    best = []
    for start in range(1, q, block):
        u = np.arange(start, min(start + block, q), dtype=np.int64)
        u = u[(u % 2 == 1) & (np.gcd(u, D) == 1)]
        u = u[(u != 1) & (u != q - 1)]
        rot = ((u % D) == 1) | ((u % D) == D - 1)
        L = np.zeros(len(u))
        for c in c_chain + c_cyc:
            L += logfac(((u * c) % q) / q)
        for j in range(s):
            r = np.exp(L + logfac(((u * 2 ** (s - j)) % q) / q) - L0)
            if j >= 1:
                r = np.where(rot, 0.0, r)
            w = comb(s - j + a, a) * r
            tot += w.sum()
            if top:
                idx = np.argsort(-w)[:top]
                best += [(float(w[i]), int(u[i]), j, float(r[i])) for i in idx]
    best.sort(reverse=True)
    return tot, best[:top]
