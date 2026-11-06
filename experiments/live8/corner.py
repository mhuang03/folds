"""corner.py N delta: witnesses of wide mixed pairs with u + 2u' >= N - 1 - delta.
Prints (orient, fam, s, a, c) where s = p (X) or q = p + 1 (Z), c = distance of b from the end."""
import sys
from wit8 import witnesses, wide

N = int(sys.argv[1])
delta = int(sys.argv[2])
umin = int(sys.argv[3]) if len(sys.argv) > 3 else 1
for u, up in wide(N):
    if u + 2 * up < N - 1 - delta or u < umin:
        continue
    v = N + 1 - up
    if (u + v) % 2 == 0:
        continue
    w = witnesses(N, u, v)
    out = []
    for (o, f, p, a, b) in w:
        s = p + 1 if f == 'Z' else p
        c = (p + 1 - b) if f == 'Z' else (p - b)
        out.append('%d%s s=%d a=%d c=%d' % (o, f, s, a, c))
    print(u, up, 'N-1-(u+2u\')=%d' % (N - 1 - u - 2 * up), len(w), '; '.join(out[:8]))
