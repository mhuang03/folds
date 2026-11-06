"""ghostpair.py N: for mixed-parity non-inward pairs {u, v}, test the two ghost reductions:
   'O': order the odd panels (but the odd one of the pair) on the background {u, v} with the
        other even panels absent, then the evens (single point in the even strip: always);
   'E': the same with the classes exchanged."""
import sys
from lib import solve, imb
from zeroset import inward_set

N = int(sys.argv[1])
cnt = {'O': 0, 'E': 0, 'none': 0, 'tot': 0}
none = []
for u in range(1, N + 1):
    for v in range(u + 1, N + 1):
        if (v - u) % 2 == 0 or inward_set(N, {u, v}):
            continue
        if (N + 1 - v, N + 1 - u) < (u, v):
            continue
        cnt['tot'] += 1
        res = ''
        for par, name in ((1, 'O'), (0, 'E')):
            tg = [x for x in range(1, N + 1) if x % 2 == par and x not in (u, v)]
            if len(tg) > 28:
                continue
            if solve(N, [u, v], tg) is not None:
                res += name
        if res:
            for c in res:
                cnt[c] += 1
        else:
            cnt['none'] += 1
            none.append((u, v))
print(N, cnt, 'neither:', none)
