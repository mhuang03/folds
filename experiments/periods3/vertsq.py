"""vertsq.py K Q1 Q2 ...: the order-Q Fourier component of c_0(T(N,K)) from the vertex formula,
for orders Q that are NEW at m = K (no face of codimension < K has an index divisible by Q), so
that the only carriers are vertices with Q | index and only the characters with all w_r != 0.
Simple vertices: ../periods2/local.py; vertices with one dependent tight row: nonsimple.py.
Vertices: Normaliz extreme rays of all class polytopes (../periods/types_K.txt).
Output: coefficient of e(-N/Q) in c_0 (comparable with fourier2.py JSON K Q K)."""
import sys
from fractions import Fraction as Fr
from math import gcd

sys.path.insert(0, '../periods')
sys.path.insert(0, '../periods2')
from verts import vertices                  # noqa: E402
from local import vertex_modes, tight_rows   # noqa: E402
from nonsimple import vertex_modes_ns        # noqa: E402

K = int(sys.argv[1])
Qs = [int(x) for x in sys.argv[2:]]
import os
TP = os.environ.get('TYPES', f'../periods/types_{K}.txt')
types = [tuple(map(int, l.split())) for l in open(TP)]
found = set()
for pi in types:
    for v in vertices(pi):
        D = 1
        for x in v:
            D = D * x.denominator // gcd(D, x.denominator)
        if any(D % q == 0 for q in Qs):
            found.add(v)
tot = {q: [0, 0] for q in Qs}
bad = 0
for v in found:
    nt = len(tight_rows(v))
    if nt == K:
        modes, _ = vertex_modes(v)
        kind = 0
    elif nt == K + 1:
        modes, _ = vertex_modes_ns(v)
        kind = 1
    else:
        bad += 1
        continue
    for q in Qs:
        tot[q][kind] += modes.get(Fr(-1, q) % 1, 0)
print(f'K={K}: {len(found)} vertices, {bad} with more than K+1 tight rows (not handled)')
for q in Qs:
    s, ns = tot[q]
    print(f'  q={q}: simple {s}   non-simple {ns}   total {s + ns}')
