"""prof.py N "bg" "prefix": imbalance profile of the unplaced panels after background + prefix,
and whether the rest satisfies the inward criterion (Theorem G) for some centre."""
import sys
from lib import imb
N = int(sys.argv[1])
bg = [int(x) for x in sys.argv[2].split()]
pre = [int(x) for x in sys.argv[3].split()] if len(sys.argv) > 3 else []
S = set(bg)
for m in pre:
    i = imb(N, S, m)
    if i:
        print('step', m, 'invalid', i)
    S.add(m)
line = []
neg, pos = [], []
for m in range(1, N + 1):
    if m in S:
        line.append('.')
    else:
        i = imb(N, S, m)
        line.append({0: '0', 1: '+', -1: '-'}.get(i, str(i) if i > 0 else chr(ord('a') - i - 2)))
        if i < 0:
            neg.append(m)
        if i > 0:
            pos.append(m)
print(''.join(line))
print('inward' if not neg or not pos or max(neg) < min(pos) else 'not inward')
