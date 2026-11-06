# genchk.py HINTS OUT.lean [N1 N2]: kernel checks (decide +kernel) of the rcov hints, one
# `example` per hint, to validate rcov.c against the Lean definitions nearTrB / nearTrP / chiXB.
import sys
hints, out = sys.argv[1], sys.argv[2]
n1, n2 = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 10**9)
L = ['import Folds.Live3r', 'open Folds Live3r', '']
cnt = 0
for line in open(hints):
    f = line.split()
    if len(f) < 6 or f[4] == 'LEFT':
        continue
    N, a, b, c = map(int, f[:4])
    if not (n1 <= N <= n2):
        continue
    if f[4] == '-':
        a, b, c = N + 1 - c, N + 1 - b, N + 1 - a
    t = f[5]
    if t == 'X':
        i, j, l = f[6:9]
        L.append('example : chiXB %d %d %d %d %s %s %s = true := by decide +kernel' % (N, a, b, c, i, j, l))
    elif t == 'R':
        k, p, u, v, y1, e1, y2, e2, i, j, l = f[6:17]
        rest = f[17:]
        if rest[0] == 'P':
            L.append('example : nearTrP %d %d %d %d %s %s %s %s %s %s %s %s %s %s %s %s %s = true := by decide +kernel'
                     % (N, a, b, c, k, p, u, v, y1, e1, y2, e2, i, j, l, rest[1], rest[2]))
        else:
            c2, ms = rest[0], rest[1:]
            L.append('example : nearTrB %d %d %d %d %s %s %s %s %s %s %s %s %s %s %s %s [%s] = true := by decide +kernel'
                     % (N, a, b, c, k, p, u, v, y1, e1, y2, e2, i, j, l, c2, ', '.join(ms)))
    cnt += 1
open(out, 'w').write('\n'.join(L) + '\n')
print(cnt, 'checks')
