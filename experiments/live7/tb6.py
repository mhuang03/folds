"""tb6.py N1 N2 [d] [e] [e']: check that TB(N, p, d; e, e'; L) is an inward window copy for ALL
p >= 1 with 2(p + 1) <= N + 1 + d and all 0 <= L <= p.  Prints the failures."""
import sys
sys.path.insert(0, '../live6')
from twoside import is_inward_copy
from tb4 import tbx

N1, N2 = int(sys.argv[1]), int(sys.argv[2])
d = int(sys.argv[3]) if len(sys.argv) > 3 else 1
e = int(sys.argv[4]) if len(sys.argv) > 4 else 0
e2 = int(sys.argv[5]) if len(sys.argv) > 5 else 1
tot = bad = 0
for N in range(N1, N2 + 1):
    for p in range(1, N + 1):
        if 2 * (p + 1) > N + 1 + d:
            break
        for L in range(0, p + 1):
            X = tbx(N, p, d, e, e2, L)
            tot += 1
            ok = all(X[i] < X[i + 1] for i in range(len(X) - 1)) and X[0] >= 1 and X[-1] <= N \
                and is_inward_copy(N, X)
            if not ok:
                bad += 1
                if bad <= 30:
                    print('FAIL', N, p, L, X)
print('total', tot, 'bad', bad)
