"""cplx.py N1 N2 [umin]: block complexity of the wide mixed pairs.
For a witness (combo, s, a, c) and a slope m: t = x - m a (left drift), t' = y - 2 - m c (X) or
y - m c (Z), where (x, y) = (u, u') (orient 0) or (u', u) (orient 1), c = distance of the right
index from the end.  complexity = min over witnesses and m in [2, 6] of max(|t|, |t'|)."""
import sys
from collections import Counter
from wit8 import witnesses, wide

N1, N2 = int(sys.argv[1]), int(sys.argv[2])
umin = int(sys.argv[3]) if len(sys.argv) > 3 else 1
MMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 6
hist = Counter()
worst = []
for N in range(N1, N2 + 1):
    for u, up in wide(N):
        if u < umin:
            continue
        v = N + 1 - up
        if (u + v) % 2 == 0:
            continue
        w = witnesses(N, u, v)
        if not w:
            continue
        best = None
        for (o, f, p, a, b) in w:
            x, y = (u, up) if o == 0 else (up, u)
            if f == 'Z':
                c = p + 1 - b
                yy = y
            else:
                c = p - b
                yy = y - 2
            for m in range(2, MMAX + 1):
                t, t2 = x - m * a, yy - m * c
                k = max(abs(t), abs(t2))
                if best is None or k < best[0]:
                    best = (k, m, o, f, p, a, c, t, t2)
        hist[best[0]] += 1
        worst.append((best[0], N, u, up, best))
print(sorted(hist.items()))
worst.sort(reverse=True)
for w in worst[:40]:
    print(w)
