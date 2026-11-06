"""shapes.py FILE u v : the slice options (side (1,0)) covering the shape (u, v) for every N in FILE."""
import sys
from collections import defaultdict

U, V = int(sys.argv[2]), int(sys.argv[3])
cnt = defaultdict(int)
tot = 0
for line in open(sys.argv[1]):
    a, b = line.split('|')
    N, u, v, c, off, old = map(int, a.split())
    if u == U and v == V:
        tot += 1
        for x in b.split():
            cnt[x] += 1
print(tot, sorted([k for k, c in cnt.items() if c == tot]))
