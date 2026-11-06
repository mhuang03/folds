"""stripsmall.py FILE : for the strip lines with small u (below the main piece's umin), the slice
options covering all N for each (e, u) (side (1, 0))."""
import sys
from collections import defaultdict
from pieces import STRIP

tot = defaultdict(int)
cnt = defaultdict(lambda: defaultdict(int))
for line in open(sys.argv[1]):
    a, b = line.split('|')
    N, u, v, c, off, old = map(int, a.split())
    if c == 2 and u < STRIP[off][1]:
        tot[(off, u)] += 1
        for x in b.split():
            cnt[(off, u)][x] += 1
for k in sorted(tot):
    print(k, tot[k], sorted([o for o, c in cnt[k].items() if c == tot[k]])[:8])
