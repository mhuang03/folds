"""wfam2.py N1 N2 d e c: for W = {floor((kK - e)/s) - c} intersected with [1, N], K = N + d, list
which s give inward window copies, with s, K mod small numbers, to find the criterion."""
import sys
sys.path.insert(0, '../live6')
from twoside import is_inward_copy

N1, N2, d, e, c = map(int, sys.argv[1:6])
for N in range(N1, N2 + 1):
    K = N + d
    good, bad = [], []
    for s in range(1, K // 2 + 1):
        W = sorted(set(x for x in ((k * K - e) // s - c for k in range(-2, s + 3)) if 1 <= x <= N))
        if not W:
            continue
        (good if is_inward_copy(N, W) else bad).append(s)
    print(N, 'good', good, 'bad', bad)
