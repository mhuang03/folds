"""lines2.py FILE : per thin line (class, offset, N mod 2): the options covering the most points,
and for the best ones the uncovered points (N, u) -- listed with u and N - 3u resp. 8u - N."""
import sys
from collections import defaultdict

pts = defaultdict(list)
for line in open(sys.argv[1]):
    a, b = line.split('|')
    N, u, v, c, off, old = map(int, a.split())
    if c in (1, 2):
        pts[(c, off, N % 2)].append((N, u, v, set(b.split())))

for key in sorted(pts):
    L = pts[key]
    cnt = defaultdict(int)
    for N, u, v, o in L:
        for x in o:
            cnt[x] += 1
    best = sorted(cnt.items(), key=lambda t: -t[1])[:3]
    print(key, len(L))
    for opt, c in best:
        left = [(N, u, N - u - 2 * v - 1) for N, u, v, o in L if opt not in o]
        us = sorted(set(x[1] for x in left))
        print('   ', opt, c, 'left', len(left), 'u values', us[:15], 'slack', sorted(set(x[2] for x in left))[:10])
