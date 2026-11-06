"""map.py FILE N: ASCII map of the lemma used per pair (from rot2z verbose output).
rows: u' (top = large), columns: u.  D = direct, 1 = Q=1, 2 = Q>=2, . = uncovered, ' ' = not wide."""
import sys
N = int(sys.argv[2])
used = {}
for line in open(sys.argv[1]):
    f = line.split()
    u, up = int(f[1]), int(f[2])
    if f[3] == 'direct':
        used[(u, up)] = 'D'
    else:
        Q = int(f[4].split('=')[1])
        used[(u, up)] = '1' if Q == 1 else '2'
W, H = 100, 50
umax = N // 3
upmax = N // 2
grid = [[' '] * W for _ in range(H)]
for u in range(1, umax + 1):
    for up in range(u, upmax + 1):
        if u + 2 * up > N - 1:
            continue
        if (u + N + 1 - up) % 2 == 0:
            continue
        c = used.get((u, up), '.')
        x = min(W - 1, u * W // (umax + 1))
        y = min(H - 1, up * H // (upmax + 1))
        cur = grid[H - 1 - y][x]
        pri = {' ': 0, 'D': 1, '1': 2, '2': 3, '.': 4}
        if pri[c] > pri[cur]:
            grid[H - 1 - y][x] = c
for row in grid:
    print(''.join(row))
