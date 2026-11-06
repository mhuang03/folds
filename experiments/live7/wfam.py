"""wfam.py N1 N2: windows of Beatty sets: W = {floor((kK - e)/s) - c : k in Z} intersected with [1, N],
for K = N + d (d = 0..4), e in {0, 1}, shift c in {0, 1, 2}, all s with K >= 2s.  Count for which
(d, e, c) every such W is an inward window copy."""
import sys
sys.path.insert(0, '../live6')
from twoside import is_inward_copy
from collections import Counter

N1, N2 = int(sys.argv[1]), int(sys.argv[2])
st = Counter()
for N in range(N1, N2 + 1):
    for d in range(0, 5):
        K = N + d
        for e in (0, 1):
            for c in (0, 1, 2):
                for s in range(1, K // 2 + 1):
                    W = sorted(set(x for x in ((k * K - e) // s - c for k in range(-2, s + 3)) if 1 <= x <= N))
                    if not W:
                        continue
                    ok = is_inward_copy(N, W)
                    st[(d, e, c, ok)] += 1
for d in range(5):
    for e in (0, 1):
        for c in (0, 1, 2):
            print(d, e, c, 'ok', st[(d, e, c, True)], 'bad', st[(d, e, c, False)])
