"""clwmap.py FILE NMIN NMAX [pairs_only] : per cell (r, delta) the min over N of the window width of each
certificate (columns of clwidth output); map of the best certificate (letter) and its width digit."""
import sys
from collections import defaultdict

nmin, nmax = int(sys.argv[2]), int(sys.argv[3])
po = len(sys.argv) > 4
mw = {}
for line in open(sys.argv[1]):
    a = line.split()
    N, r, d, pair = int(a[0]), int(a[1]), int(a[2]), int(a[3])
    if not (nmin <= N <= nmax) or (po and not pair):
        continue
    ws = [float(x) for x in a[4:]]
    if (r, d) in mw:
        mw[(r, d)] = [min(x, y) for x, y in zip(mw[(r, d)], ws)]
    else:
        mw[(r, d)] = ws
rs = sorted(set(r for r, d in mw))
ds = sorted(set(d for r, d in mw))
for r in rs:
    row = ''
    for d in ds:
        if (r, d) not in mw:
            row += '  '
            continue
        ws = mw[(r, d)]
        k = max(range(len(ws)), key=lambda i: ws[i])
        w = ws[k]
        row += (chr(97 + k) + (str(min(9, int(w * 10))) if w >= 0 else '-')) if w >= 0 else '..'
    print('%4d %s' % (r, row))
