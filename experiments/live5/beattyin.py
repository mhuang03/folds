"""beattyin.py N p: the Beatty copies X(N, p, h) = {(rN - h) // p : r = 1..p}, h + 2p <= N + 1,
with their imbalance profile (outside X) and whether they are inward."""
import sys
from lib import imb

N, p = int(sys.argv[1]), int(sys.argv[2])
for h in range(0, N + 2 - 2 * p):
    X = [(r * N - h) // p for r in range(1, p + 1)]
    S = set(X)
    prof = ''
    neg, pos = [], []
    for m in range(1, N + 1):
        if m in S:
            prof += '|'
            continue
        i = imb(N, S, m)
        prof += {0: '.', 1: '+', -1: '-'}.get(i, '*')
        if i < 0:
            neg.append(m)
        if i > 0:
            pos.append(m)
    ok = not neg or not pos or max(neg) < min(pos)
    print(f'h={h:3d} {"IN " if ok else "   "} {prof} {X}')
