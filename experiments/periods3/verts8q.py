"""verts8q.py: the order-120 and order-40 Fourier components of the constant term c_0(N) of T(N,8).

120 = 2^3 (2^4 - 1) and 40 = 2^3 5 are "new at m = 8": no face of codimension <= 7 has an index
divisible by them (5 | 2^s - 1 needs s = 4, and 8 | index needs a = 3 more halvings: a + s = 7).
So by the face lemma the exact-order-q part of c_0(T(N,8)) is the sum, over the DISTINCT vertices
v of the k = 8 class polytopes with q | index(v), of the vertex formula of ../periods2 local.py
(characters with all w_r != 0; each vertex once, with all its valid local cells).
A nonzero value shows that the 5-part of B(8) divides the period of T(N,8).
Vertices: Normaliz extreme rays of every class polytope (types from ../periods/types_8.txt).
"""
import sys
import time
from fractions import Fraction as Fr
from math import gcd

sys.path.insert(0, '../periods')
sys.path.insert(0, '../periods2')
from verts import vertices          # noqa: E402
from local import vertex_modes      # noqa: E402


def lcm(a, b):
    return a * b // gcd(a, b)


types = [tuple(map(int, l.split())) for l in open('../periods/types_8.txt')]
t0 = time.time()
found = {}
for i, pi in enumerate(types):
    for v in vertices(pi):
        D = 1
        for x in v:
            D = lcm(D, x.denominator)
        if D % 40 == 0:
            found.setdefault(v, D)
    if i % 2000 == 0:
        print(f'  {i}/{len(types)} polytopes, {len(found)} vertices with 40 | index, {time.time()-t0:.0f}s',
              flush=True)
print(f'{len(found)} distinct vertices with 40 | index:',
      {d: sum(1 for x in found.values() if x == d) for d in set(found.values())}, flush=True)
with open('verts8_40.txt', 'w') as f:
    for v, D in found.items():
        f.write(f'{D} ' + ' '.join(str(x) for x in v) + '\n')
tot = {120: 0, 40: 0}
nval = {120: 0, 40: 0}
skipped = 0
for v, D in found.items():
    try:
        modes, nc = vertex_modes(v)
    except AssertionError:
        skipped += 1
        continue
    for q in (120, 40):
        c = modes.get(Fr(-1, q) % 1, 0)
        if c:
            nval[q] += 1
        tot[q] += c
for q in (120, 40):
    print(f'order {q}: {nval[q]} valid vertices carry it; coefficient of e(-N/{q}) in c_0(T(N,8)) = {tot[q]}')
print('non-simple vertices skipped:', skipped)
