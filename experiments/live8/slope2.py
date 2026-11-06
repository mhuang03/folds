"""slope2.py N1 N2: for each wide mixed pair, the witnesses in slope-2 coordinates:
combo (orient, fam), e = K - 2s, t1 = floor(L e / K)-ish (block of the left element).
Reports, per pair, the minimal t1 over all witnesses, and a histogram."""
import sys
from collections import Counter
from wit8 import witnesses, wide

N1, N2 = int(sys.argv[1]), int(sys.argv[2])
hist = Counter()
worst = []
for N in range(N1, N2 + 1):
    for u, up in wide(N):
        v = N + 1 - up
        if (u + v) % 2 == 0:
            continue
        w = witnesses(N, u, v)
        if not w:
            continue
        best = None
        for (o, f, p, a, b) in w:
            x = u if o == 0 else up
            # left element x has index a: x = 2a + t1
            t1 = x - 2 * a
            if best is None or t1 < best[0]:
                best = (t1, o, f, p, a, b)
        hist[best[0]] += 1
        worst.append((best[0], N, u, up, best))
print(sorted(hist.items()))
worst.sort(reverse=True)
for w in worst[:30]:
    print(w)
