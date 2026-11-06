"""lines.py FILE... : per thin line (class, offset, N mod 2), which slice options cover the most
points; greedy cover, reporting for each chosen option the u-range (as fractions of N)."""
import sys
from collections import defaultdict

pts = defaultdict(list)  # key -> list of (N, u, opts)
for fn in sys.argv[1:]:
    for line in open(fn):
        a, b = line.split('|')
        N, u, v, c, off, old = map(int, a.split())
        opts = set(b.split())
        if c in (1, 2):
            pts[(c, off, N % 2)].append((N, u, v, opts, old))

for key in sorted(pts):
    L = pts[key]
    cnt = defaultdict(int)
    for N, u, v, o, old in L:
        for x in o:
            cnt[x] += 1
    best = sorted(cnt.items(), key=lambda t: -t[1])[:4]
    left = [(N, u) for N, u, v, o, old in L if best and best[0][0] not in o]
    print(key, len(L), best, 'left by best:', left[:12], len(left))
