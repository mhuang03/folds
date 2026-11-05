"""Test explicit weight families w for the aggregated certificate: is
min_c sum_m w(m) D_m(c) > 0 over ALL labellings c with t labels?  (lpcert.pricing, MILP)
usage: wfamily.py t Nmin Nmax family     family in: one, invr, invr2, invsqrt"""
import sys, math
import numpy as np
from lpcert import pricing, Dvec

def weights(N, fam):
    w = []
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if r == 0: w.append(0.0); continue
        w.append({'one': 1.0, 'invr': 1.0 / r, 'invr2': 1.0 / r ** 2, 'invsqrt': r ** -0.5,
                  'invrlog': 1.0 / (r * (1 + math.log2(r)))}[fam])
    return np.array(w)

t, a, b, fam = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
for N in range(a, b + 1):
    w = weights(N, fam)
    val, c = pricing(N, t, w)
    print(f't={t} N={N} {fam}: min = {val:.4f}', 'CERT' if val > 1e-9 else '', ''.join(map(str, c)), flush=True)
