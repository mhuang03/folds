"""clbound.py FILE NMIN NMAX NAME... : for each named (o f dir) certificate, per r the delta-range
where it is valid on all sampled N (cells with points)."""
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
for nm in sys.argv[4:]:
    k = NAMES.index(nm)
    print(nm)
    for r in sorted(set(r for r, d in cell)):
        ds = sorted(d for rr, d in cell if rr == r)
        ok = [d for d in ds if cell[(r, d)] >> k & 1]
        # maximal runs
        runs = []
        for d in ok:
            if runs and d == runs[-1][1] + 1:
                runs[-1][1] = d
            else:
                runs.append([d, d])
        print('  r=%d %s' % (r, runs))
