"""Imbalance profile during the near greedy: for each unplaced panel m, L - R (placed counts in
its window arms).  Printed as a row of signed digits ('.' placed, 'x' removed)."""
import sys
from neargreedy import greedy, arms

N, a, b = map(int, sys.argv[1:4])
D = set(range(a, b + 1))
seq = greedy(N, D, a + b)
S = set()


def row():
    out = []
    for m in range(1, N + 1):
        if m in D:
            out.append('  x')
        elif m in S:
            out.append('  .')
        else:
            L, R = arms(N, m)
            out.append('%3d' % (sum(x in S for x in L) - sum(x in S for x in R)))
    return ''.join(out)


print('    ' + ''.join('%3d' % m for m in range(1, N + 1)))
print('    ' + row())
for m in seq:
    S.add(m)
    print('%3d ' % m + row())
