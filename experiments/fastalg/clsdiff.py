"""Where do bisimilar sets differ?  python3 clsdiff.py N k
For every live k-set S with class c, compare S with the class representative R (the
smallest member) or its mirror, whichever is closer in Hamming distance.  Prints how
often each panel position lies in the difference, and the distance histogram."""
import sys
from collections import defaultdict, Counter
from common import tables, bisimF

N = int(sys.argv[1])
k = int(sys.argv[2])
valid, g, f = tables(N)
cls = bisimF(N, valid, g, f)


def mir(s):
    return int(format(s, '0%db' % N)[::-1], 2)


rep = {}
pos = Counter()
dist = Counter()
nonmir = 0
for s in range(1 << N):
    if bin(s).count('1') != k or not (g[s] and f[s]):
        continue
    c = cls[s]
    if c not in rep:
        rep[c] = s
        continue
    R = rep[c]
    d1 = s ^ R
    d2 = s ^ mir(R)
    d = d1 if bin(d1).count('1') <= bin(d2).count('1') else d2
    if d == 0:
        continue
    nonmir += 1
    dist[bin(d).count('1')] += 1
    for p in range(N):
        if d >> p & 1:
            pos[p + 1] += 1
print('N', N, 'k', k, 'classes', len(rep), 'non-mirror merged sets', nonmir)
print('hamming distance to representative:', sorted(dist.items()))
print('panel m : count')
print(' '.join('%d:%d' % (m, pos[m]) for m in range(1, N + 1)))
