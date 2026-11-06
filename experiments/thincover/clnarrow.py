"""clnarrow.py FILE THR [NMIN NMAX] : cells whose best certificate (max over columns of the min over N of
the width) is below THR; prints the cells and the best column."""
import sys
args = open('tmp/args.txt').read().split() if len(sys.argv) > 5 else None
thr = float(sys.argv[2])
nmin = int(sys.argv[3]) if len(sys.argv) > 3 else 0
nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
mw = {}
for line in open(sys.argv[1]):
    a = line.split()
    N, r, d, pair = int(a[0]), int(a[1]), int(a[2]), int(a[3])
    if not (nmin <= N <= nmax):
        continue
    ws = [float(x) for x in a[4:]]
    mw[(r, d)] = [min(x, y) for x, y in zip(mw[(r, d)], ws)] if (r, d) in mw else ws
ALLD = [(1, 1), (2, 1), (3, 2), (1, 2), (2, 3), (3, 1), (4, 3), (5, 3), (3, 4), (5, 4), (1, 0), (0, 1)]
names = ['o%df%d%s' % (o, f, d) for o in range(2) for f in range(3) for d in ALLD]
bad = []
for c, ws in sorted(mw.items()):
    k = max(range(len(ws)), key=lambda i: ws[i])
    if ws[k] < thr:
        bad.append((c, ws[k], names[k] if len(ws) == len(names) else k))
print(len(bad), 'of', len(mw))
for b in bad:
    print(b)
