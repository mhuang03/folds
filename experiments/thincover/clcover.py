"""clcover.py FILE NMIN NMAX : greedy cover of the cluster cells (r, delta) by (o, f, dir) with
ParOK of famCons valid for all sampled N in [NMIN, NMAX] in the cell; prints the map."""
import sys
from collections import defaultdict

DIRS = [(1, 1), (2, 1), (3, 2), (3, 1), (4, 3), (5, 3), (1, 2), (2, 3), (3, 4), (5, 7), (1, 0), (0, 1), (4, 1), (5, 2), (5, 4), (7, 4)]
NAMES = ['o%df%d(%d,%d)' % (o, f, d[0], d[1]) for o in range(2) for f in range(3) for d in DIRS]
nmin, nmax = int(sys.argv[2]), int(sys.argv[3])
cell = {}
for line in open(sys.argv[1]):
    N, u, v, r, dl, bits = line.split()
    N, r, dl = int(N), int(r), int(dl)
    if nmin <= N <= nmax:
        b = int(bits[::-1], 2)
        cell[(r, dl)] = cell.get((r, dl), (1 << len(bits)) - 1) & b
left = set(cell)
chosen = []
while left:
    cnt = defaultdict(int)
    for c in left:
        b = cell[c]
        i = 0
        while b:
            if b & 1:
                cnt[i] += 1
            b >>= 1
            i += 1
    if not cnt:
        break
    k = max(cnt, key=lambda x: cnt[x])
    chosen.append(k)
    left -= set(c for c in left if cell[c] >> k & 1)
print('chosen', [(chr(97 + i), NAMES[k]) for i, k in enumerate(chosen)], 'uncovered', len(left))
rs = sorted(set(r for r, d in cell))
ds = sorted(set(d for r, d in cell))
for r in rs:
    row = ''
    for d in ds:
        if (r, d) not in cell:
            row += ' '
            continue
        ch = '.'
        for i, k in enumerate(chosen):
            if cell[(r, d)] >> k & 1:
                ch = chr(97 + i)
                break
        row += ch
    print('%4d %s' % (r, row))
