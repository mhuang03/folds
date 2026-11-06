"""swap2.py N1 N2 c: like swap.py but prints, per N, the (p, h) that are inward copies after
moving the last element to N - c, summarised as: failures with p odd and the min alpha of
successes / the successes with p even."""
import sys
from swap import swapped
from twoside import is_inward_copy

N1, N2, c = map(int, sys.argv[1:4])
for N in range(N1, N2 + 1):
    fo, se = [], []
    for p in range(3, (N + 1) // 2 + 1):
        for h in (0, 1):
            if h + 2 * p > N + 1:
                continue
            X = swapped(N, p, h, c)
            if X[-2] >= X[-1]:
                continue
            ok = is_inward_copy(N, X)
            if p % 2 == 1 and not ok and N >= (c + 2) * p + h:
                fo.append((p, h))
            if p % 2 == 0 and ok:
                se.append((p, h))
    if fo or se:
        print(N, 'odd failures', fo, 'even successes', se)
