"""probe6.py M WORD: per-placement valid intervals of one free point at a chain vertex."""
import sys
from fractions import Fraction as Fr
from chainface import weight, chain_values
sys.path.insert(0, '../periods2')
from face import breakpoints

M = int(sys.argv[1])
n = M - 1
w = sys.argv[2]
bits = {'W1': (1,) + (0,) * (n - 1), 'W3': (1,) * n, 'W2': (1, 1) + (0,) * (n - 2)}.get(w)
if bits is None:
    bits = tuple(int(c) for c in w)
eps = Fr(1, 2 ** (n + 40))
v = chain_values(bits, eps)
P = 2 ** n
print('v*2^n =', [float(x * P) for x in v])
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
        s = weight(seq, cyc, bits)
        if s:
            if segs and abs(segs[-1][1] - x0) < Fr(1, 2 ** (n + 20)) and segs[-1][2] == s:
                segs[-1][1] = x1
            else:
                segs.append([x0, x1, s])
    tot = sum(s * (b - a) for a, b, s in segs)
    print(f'p={p}:', '  '.join(f'[{float(a*P):.3f},{float(b*P):.3f}]/2^n {"+" if s>0 else "-"}' for a, b, s in segs),
          f' tot*2^n={float(tot*P):.4f}')
