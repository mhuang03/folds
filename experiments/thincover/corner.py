"""corner.py FILE d : for the diagonal line d, group the points by m = N - 3u and list the options
covering all of them (u > 4)."""
import sys
from collections import defaultdict

d = int(sys.argv[2])
tot = defaultdict(int)
cnt = defaultdict(lambda: defaultdict(int))
for line in open(sys.argv[1]):
    a, b = line.split('|')
    N, u, v, c, off, old = map(int, a.split())
    if c == 1 and off == d and u > 4:
        m = N - 3 * u
        tot[m] += 1
        for x in b.split():
            cnt[m][x] += 1
for m in sorted(tot):
    if m > 40:
        break
    print(m, tot[m], sorted([k for k, c in cnt[m].items() if c == tot[m]]))
