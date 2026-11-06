"""probe2.py M [A]: per-placement structure of the one-free-point weight at theta = A/D."""
import sys
sys.path.insert(0, '../periods2')
from face import orbit, weight, breakpoints
from fractions import Fraction as Fr

M = int(sys.argv[1])
A = int(sys.argv[2]) if len(sys.argv) > 2 else 1
D = 2 ** (M - 1) - 1
v, bits = orbit(M, A)
print('v*D =', [x * D for x in v], 'bits', bits)
K = M + 1
for p in range(K):
    cyc = [t for t in range(K) if t != p]
    B = breakpoints(v)
    segs = []
    for x0, x1 in zip(B, B[1:]):
        seq = [None] * K
        for t, val in zip(cyc, v):
            seq[t] = val
        seq[p] = (x0 + x1) / 2
        w = weight(seq, cyc, bits)
        if w:
            if segs and segs[-1][1] == x0 and segs[-1][2] == w:
                segs[-1][1] = x1
            else:
                segs.append([x0, x1, w])
    tot = {}
    for a, b, w in segs:
        tot[w[1]] = tot.get(w[1], 0) + w[0] * (b - a)
    print(f'p={p}:', '  '.join(f'[{a*D},{b*D}]/D {"+" if w[0]>0 else "-"}{w[1][0]}' for a, b, w in segs),
          ' tot*D:', {k: x * D for k, x in tot.items()})
