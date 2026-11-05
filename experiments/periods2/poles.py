"""poles.py JSON K: the exact pole order e_q of F_K(t) = sum_N T(N,K) t^N at the primitive q-th
roots of unity, for every q dividing some class denominator exponent, i.e. the cyclotomic
factorisation of the REDUCED denominator, without forming the rational function: e_q is the
largest r such that the summed Laurent coefficient lim (1 - t/zeta)^r F_K(t) is nonzero, each
class numerator being divided exactly (over Z) by the appropriate power of Phi_q (fourier2.py
A_exact).  Compared with the staircase prediction e_q = K + 1 - m(q) (gf.py m_of)."""
import sys
import json
import os
import mpmath as mp
from fourier2 import A_exact, cyclo
from gf import m_of

mp.mp.dps = int(os.environ.get('DPS', '80'))

if __name__ == '__main__':
    path, K = sys.argv[1], int(sys.argv[2])
    cls = [json.loads(l) for l in open(path)]
    qs = set()
    for cl in cls:
        for d in cl['den']:
            qs |= {q for q in range(2, d + 1) if d % q == 0}
    res = {}
    for q in sorted(qs):
        phi = cyclo(q)
        zeta = mp.exp(2j * mp.pi / q)
        rmax = max(sum(1 for d in cl['den'] if d % q == 0) for cl in cls)
        e = 0
        for r in range(rmax, 0, -1):
            tot = sum(A_exact(cl, q, r, phi, zeta) for cl in cls)
            if abs(tot) > mp.mpf(10) ** -30:
                e = r
                break
        res[q] = e
        pred = K + 1 - m_of(q) if m_of(q) <= K else 0
        flag = '' if e == pred else '   <-- differs from staircase prediction'
        if e or pred:
            print(f'  q={q:4d}: pole order {e}  (prediction {pred}){flag}', flush=True)
    print(f'K={K}: reduced denominator = Phi_1^{K+1} * prod_q Phi_q^e_q over the q above')
