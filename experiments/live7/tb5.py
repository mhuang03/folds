"""tb5.py N1 N2 d: for TB(N, p, d; e, e'; L) (tb4.tbx) list which (p, e, e', L - R) fail to be
inward window copies, for slope (N+1+d)/(p+1) >= 2."""
import sys
from collections import Counter
sys.path.insert(0, '../live6')
from twoside import is_inward_copy
from tb4 import tbx

N1, N2, d = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
st = Counter()
fails = []
for N in range(N1, N2 + 1):
    for p in range(2, (N + 1 + d) // 2):
        for e in (0, 1):
            for e2 in (0, 1):
                for L in range(1, p):
                    R = p - L
                    X = tbx(N, p, d, e, e2, L)
                    ok = all(X[i] < X[i + 1] for i in range(len(X) - 1)) and is_inward_copy(N, X)
                    key = (e, e2, L - R)
                    st[(key, ok)] += 1
                    if not ok and abs(L - R) <= 1:
                        fails.append((N, p, e, e2, L, R, '%.2f' % ((N + 1 + d) / (p + 1))))
for k in sorted(set(k for k, _ in st)):
    if abs(k[2]) <= 4:
        print(k, 'ok', st[(k, True)], 'fail', st[(k, False)])
print(len(fails), fails[:40])
