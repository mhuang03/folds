# pat3.py N0 N1: N = 3 mod 4, c = 3 mod 4 (moved phiE, c = 2g + 1): try the step pattern
# 5, 4, 3, (N + 7)/2 [, extra] on the image and report where Theorem G (centre 1/2) holds.
import sys
from base import *
from moved import maps_for

def run(N, B, steps):
    B = set(B)
    for m in steps:
        if not valid(N, B, m): return None
        B.add(m)
    return B

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    if N % 4 != 3: continue
    row = []
    for c in range(7, N - 3, 4):
        p, g, f = maps_for(N, c)
        if not (3 <= g <= p - 2): continue
        img = {f(y) for y in range(1, p + 1)}
        res = '-'
        for name, st in [('a', [5]), ('b', [5, 4, 3, (N + 7) // 2])]:
            B = run(N, img, st)
            if B is not None and inward1(N, B): res = name; break
        row.append('%d:%s' % (c, res))
    print(N, ' '.join(row))
