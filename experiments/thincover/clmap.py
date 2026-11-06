"""clmap.py FILE NMIN NMAX : map of the cluster box in (r = 4u - N, delta) for NMIN <= N <= NMAX:
per cell the certificates valid for every point in the cell:
A keyA, 4 keyB4, 1 keyB1, D regD, B regB/B2, k: some edge-library key, P: ParOK side (3,2)/(2,3),
'.': nothing common, ' ': no point."""
import sys
from collections import defaultdict

nmin, nmax = int(sys.argv[2]), int(sys.argv[3])
cell = defaultdict(list)
for line in open(sys.argv[1]):
    N, u, v, r, dl, ob, kA, k4, k1, k, pf = map(int, line.split())
    if nmin <= N <= nmax:
        cell[(r, dl)].append((ob, kA, k4, k1, k, pf))
rs = sorted(set(r for r, d in cell))
ds = sorted(set(d for r, d in cell))


def code(L):
    if all(x[1] for x in L):
        return 'A'
    if all(x[3] for x in L):
        return '1'
    if all(x[2] for x in L):
        return '4'
    if all(x[0] & 8 for x in L):
        return 'D'
    if all(x[0] & 3 for x in L):
        return 'B'
    if all(x[4] >= 0 for x in L):
        return 'k'
    if all(x[5] for x in L):
        return 'P'
    if all(x[1] or x[3] for x in L):
        return 'a'
    return '.'


print('     ' + ''.join(('%d' % (abs(d) // 10 % 10)) for d in ds))
print('     ' + ''.join(('%d' % (abs(d) % 10)) for d in ds))
for r in rs:
    print('%4d ' % r + ''.join(code(cell[(r, d)]) if (r, d) in cell else ' ' for d in ds))
