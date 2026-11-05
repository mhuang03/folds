"""period.py FILE COL DEG [NMIN]: find the smallest L such that the (DEG+1)-fold L-step
difference of the column vanishes for all N >= NMIN (=> quasi-polynomial of period L)."""
import sys
from math import comb
d = {}
for l in open(sys.argv[1]):
    t = l.split()
    if len(t) > int(sys.argv[2]) and t[0].isdigit():
        d[int(t[0])] = int(t[int(sys.argv[2])])
deg = int(sys.argv[3])
nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1
M = max(d)
for L in range(1, (M - nmin) // (deg + 1) + 1):
    bad = []
    ok = 0
    for n in range(nmin, M - (deg + 1) * L + 1):
        s = sum((-1) ** (deg + 1 - i) * comb(deg + 1, i) * d[n + i * L] for i in range(deg + 2))
        if s:
            bad.append(n)
        else:
            ok += 1
    if not bad:
        print('L =', L, 'works,', ok, 'checks')
        break
    if len(bad) < 10:
        print('L =', L, 'fails only at N =', bad)
else:
    print('no L up to', (M - nmin) // (deg + 1))
