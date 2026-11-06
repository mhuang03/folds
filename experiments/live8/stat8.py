"""stat8.py N1 N2: for wide mixed pairs, which (orient, family) combos have witnesses, by d = u'-u."""
import sys
from collections import defaultdict
from wit8 import witnesses, wide

N1, N2 = int(sys.argv[1]), int(sys.argv[2])
dmax = int(sys.argv[3]) if len(sys.argv) > 3 else 6
stat = defaultdict(lambda: defaultdict(int))
tot = defaultdict(int)
for N in range(N1, N2 + 1):
    for u, up in wide(N):
        v = N + 1 - up
        if (u + v) % 2 == 0:
            continue
        d = min(up - u, dmax)
        w = witnesses(N, u, v)
        combos = set((o, f) for (o, f, p, a, b) in w)
        tot[d] += 1
        for c in combos:
            stat[d][c] += 1
        if not combos:
            stat[d]['none'] += 1
for d in sorted(tot):
    print(d, tot[d], dict(stat[d]))
