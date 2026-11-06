"""small.py N1 N2: the pairs with u <= 3 (mixed, wide) that fail dirAny in both orientations."""
import sys
from collections import Counter


def dirOK(K, L, R, al, be, smax, a):
    S2 = min(max(a * K - al, 0) // L, smax)
    S1 = max((max(a * K - al, 0) + 1 + L) // (L + 1), R, 2)
    if S1 > S2:
        return False
    hi = max(S2 * R + be + S2 - 1, 0)
    return S1 * R + be <= (hi // K) * K


def dirAll(N, x, y, a):
    if dirOK(N + 2, x, y, 0, 1, (N + 2) // 2, a):
        return True
    if y >= 2 and dirOK(N, x, y - 2, 0, 1, (N + 1) // 2, a):
        return True
    if y >= 2 and dirOK(N, x, y - 2, 1, 0, N // 2, a):
        return True
    return False


def dirAny(N, x, y):
    return any(dirAll(N, x, y, a) for a in range(2, x + 2))


cnt = Counter()
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for u in (1, 2, 3):
        for v in range(max(2 * u + 2, (N + u + 4) // 2), N + 2 - u):
            if (u + v) % 2 != 1:
                continue
            if u == 1 and v == N:
                continue
            up = N + 1 - v
            if dirAny(N, u, up) or dirAny(N, up, u):
                continue
            key = (u, up if up < 20 else 'u\'=%d (N-2u\')=%d' % (up, N - 2 * up))
            cnt[(u, up if up < 12 else 'big')] += 1
            if u > 1 and up >= 12:
                print(N, u, up, 'N - 3u\' =', N - 3 * up, 'N-2u\' =', N - 2 * up)
print(sorted(cnt.items(), key=str))
