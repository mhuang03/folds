"""zcheck.py N1 N2: the centred Beatty sets Z(N, p) = {floor(k(N+2)/(p+1)) : 1 <= k <= p}, 2p <= N:
check that every one is an inward window copy (I = 0 on Z, imbalances outside: all negative ones
left of all positive ones); report the possible centres."""
import sys
sys.path.insert(0, '../live6')
from twoside import imb_all


def Z(N, p):
    return [k * (N + 2) // (p + 1) for k in range(1, p + 1)]


bad = 0
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for p in range(1, N // 2 + 1):
        X = Z(N, p)
        ind, I = imb_all(N, X)
        if any(I[x] for x in X):
            bad += 1; print('not a copy', N, p); continue
        neg = [m for m in range(1, N + 1) if not ind[m] and I[m] < 0]
        pos = [m for m in range(1, N + 1) if not ind[m] and I[m] > 0]
        if neg and pos and max(neg) > min(pos):
            bad += 1; print('not inward', N, p)
        if len(sys.argv) > 3:
            print(N, p, 'maxneg', max(neg) if neg else None, 'minpos', min(pos) if pos else None)
print('bad', bad)
