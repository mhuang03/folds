"""crudetop.py S A [NTOP]: the largest terms C(S-j+A, A) * ratio(u, j) of the crude tail, with the
structure (z chain, attachment value, theta) and whether it has a valid time order."""
import sys
from math import comb
import numpy as np
from topcheck import ratios, structure
from mixed import interleavings, vertex_term

s, a = int(sys.argv[1]), int(sys.argv[2])
ntop = int(sys.argv[3]) if len(sys.argv) > 3 else 25
q = 2 ** a * (2 ** s - 1)
L = []
for u, j, r in ratios(s, a):
    w = comb(s - j + a, a) * r
    idx = np.argsort(-w)[:ntop]
    L += [(float(w[i]), int(u[i]), j, float(r[i])) for i in idx]
L.sort(reverse=True)
for w, u, j, r in L[:ntop]:
    orb, z = structure(u, j, s, a)
    nv = sum(1 for y, _ in interleavings(orb, j, z) if vertex_term(y, q)[0] is not None)
    uc = u if u < q // 2 else u - q
    print(f'u={uc:8d} (u mod 2^a={u % 2**a}, q/2-type={min(u % (q//2), q//2 - u % (q//2))}) j={j:2d} '
          f'ratio={r:.3g} C*ratio={w:.3g} V={nv}  theta*D={orb[0]*(2**s-1)} attach*D={orb[j]*(2**s-1)} '
          f'z*q={[int(x*q) for x in z]}')
