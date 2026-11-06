"""clkeys.py FILE NMIN NMAX : greedy cover of the cluster cells (r, delta) by single certificates
valid on the whole cell (all sampled N in [NMIN, NMAX]); prints a map with one letter per key."""
import sys
from collections import defaultdict

KC = [(0,1,1,1,4),(0,1,2,1,4),(0,1,2,1,1),(1,1,1,1,4),(1,1,2,1,4),(1,1,2,1,1),(2,1,1,1,4),(2,1,2,1,4),(2,1,2,1,1),
      (0,1,3,2,4),(0,1,3,2,1),(1,1,3,2,4),(1,1,3,2,1),(0,1,1,1,1),(1,1,1,1,1),
      (0,0,1,1,4),(0,0,1,1,1),(1,0,1,1,4),(1,0,1,1,1),(0,1,3,1,4),(0,1,3,1,1),(1,1,3,1,1),(1,1,3,1,4),
      (0,1,4,3,4),(0,1,4,3,1),(1,1,4,3,4),(1,1,4,3,1),(0,1,5,3,1),(0,1,5,3,4),(1,1,5,3,1),(1,1,5,3,4)]
nmin, nmax = int(sys.argv[2]), int(sys.argv[3])
cell = defaultdict(list)
for line in open(sys.argv[1]):
    N, u, v, r, dl, ob, kA, k4, k1, k, pf = map(int, line.split())
    if nmin <= N <= nmax:
        bits = set(i for i in range(len(KC)) if k >> i & 1)
        if ob & 8:
            bits.add('D')
        if ob & 3:
            bits.add('B')
        if pf:
            bits.add('P')
        cell[(r, dl)].append(bits)
valid = {c: set.intersection(*L) for c, L in cell.items()}
left = set(c for c in cell)
chosen = []
while left:
    cnt = defaultdict(int)
    for c in left:
        for b in valid[c]:
            cnt[b] += 1
    if not cnt:
        break
    b = max(cnt, key=lambda x: cnt[x])
    chosen.append(b)
    left -= set(c for c in left if b in valid[c])
print('chosen', [(b, KC[b] if isinstance(b, int) else b) for b in chosen], 'uncovered', len(left))
let = {b: chr(ord('a') + i) for i, b in enumerate(chosen)}
rs = sorted(set(r for r, d in cell))
ds = sorted(set(d for r, d in cell))
for r in rs:
    row = ''
    for d in ds:
        if (r, d) not in cell:
            row += ' '
            continue
        ch = '.'
        for b in chosen:
            if b in valid[(r, d)]:
                ch = let[b]
                break
        row += ch
    print('%4d %s' % (r, row))
