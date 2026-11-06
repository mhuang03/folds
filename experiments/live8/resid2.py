"""resid2.py N: residual of the EXACT direct predicates (any a, families Z, X0, X1, both
orientations, union containing a multiple of K) together with settled_evenEven."""
import sys

N = int(sys.argv[1])
M = N + 2


def direct_exact(K, L, R, al, be, smax, amin=2):
    if L < 1 or R < 0:
        return False
    for a in range(amin, L + 1):
        S2 = min((a * K - al) // L, smax)
        S1 = max(-(-(a * K - al + 1) // (L + 1)), R, 2)
        if S1 > S2:
            if (a * K - al) // L > smax and S1 > smax:
                break
            continue
        lo, hi = S1 * R + be, S2 * R + be + S2 - 1
        if (hi // K) * K >= lo:
            return True
    return False


def covered(u, up):
    if N % 2 == 0 and u % 2 == 0 and up % 2 == 0:
        return True
    for (x, y) in ((u, up), (up, u)):
        if direct_exact(M, x, y, 0, 1, M // 2):
            return True
        if direct_exact(N, x, y - 2, 0, 1, (N + 1) // 2):
            return True
        if direct_exact(N, x, y - 2, 1, 0, N // 2):
            return True
    return False


tot = res = 0
W, H = 90, 40
grid = [[' '] * W for _ in range(H)]
for u in range(1, N):
    for up in range(u, N):
        if u + 2 * up > N - 1:
            break
        if (u + N + 1 - up) % 2 == 0:
            continue
        tot += 1
        cov = covered(u, up)
        if not cov:
            res += 1
        x = min(W - 1, u * W // (N // 3 + 1))
        y = min(H - 1, up * H // (N // 2 + 1))
        if grid[H - 1 - y][x] != '#':
            grid[H - 1 - y][x] = '.' if cov else '#'
print('N', N, 'wide mixed', tot, 'residual', res, '%.1f%%' % (100.0 * res / tot))
for row in grid:
    print(''.join(row))

if len(sys.argv) > 2:
    from collections import defaultdict
    d = defaultdict(list)
    for u in range(1, N):
        for up in range(u, N):
            if u + 2 * up > N - 1:
                break
            if (u + N + 1 - up) % 2 == 0:
                continue
            if not covered(u, up):
                d[u].append((up, N - 1 - u - 2 * up))
    for u in sorted(d):
        print(u, len(d[u]), 'delta range', min(x[1] for x in d[u]), max(x[1] for x in d[u]),
              d[u][:6])
