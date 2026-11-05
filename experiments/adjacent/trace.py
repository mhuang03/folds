"""Trace the near greedy: print the state string after each step ('#' placed, 'x' removed,
'.' empty) and the set of valid panels."""
import sys
from neargreedy import greedy, arms

N, a, b = map(int, sys.argv[1:4])
tie = int(sys.argv[4]) if len(sys.argv) > 4 else 1
D = set(range(a, b + 1)) if a > 0 else set()
c2 = a + b if a > 0 else int(sys.argv[5])
seq = greedy(N, D, c2, tie)
print(seq)
S = set()
for m in seq:
    S.add(m)
    s = ''.join('x' if i in D else ('#' if i in S else '.') for i in range(1, N + 1))
    valid = [x for x in range(1, N + 1) if x not in S and x not in D and
             sum(y in S for y in arms(N, x)[0]) == sum(y in S for y in arms(N, x)[1])]
    print('%3d %s  valid next: %s' % (m, s, valid))
