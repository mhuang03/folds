"""resid.py N: the residual region of Live8 (mixed-parity wide pairs not covered by the proven
families settled_evenEven and settled_directZ_region), with a coarse map.
Map: rows u' (top = large), columns u; '#' residual, '.' covered."""
import sys

N = int(sys.argv[1])
M = N + 2


def evenEven(u, up):
    return N % 2 == 0 and u % 2 == 0 and up % 2 == 0


def regionD(u, up):
    if u < 4 or u > up or u + up > N:
        return False
    r = u % 2
    CA = (u - r) * M * (u + up + 1) >= 2 * (u + 1) * (M * u + 2 * u * up + u)
    CB = (u * M - r * M - 2 * u + 2) * (up + 1) >= 2 * u * (up * up + M)
    return CA and CB


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
        cov = evenEven(u, up) or regionD(u, up)
        if not cov:
            res += 1
        x = min(W - 1, u * W // (N // 3 + 1))
        y = min(H - 1, up * H // (N // 2 + 1))
        c = '.' if cov else '#'
        if grid[H - 1 - y][x] != '#':
            grid[H - 1 - y][x] = c
print('N', N, 'wide mixed', tot, 'residual', res, '%.1f%%' % (100.0 * res / tot))
for row in grid:
    print(''.join(row))
