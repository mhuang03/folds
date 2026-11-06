# Near copies [p] -> [N] fixing 1 -> 1, 2 -> 2: regularity at the panels j >= 3, and whether the
# image satisfies Theorem G after a few valid steps (so its complement is ordered from scratch).
import sys
from base import *

def rel(n, j, y):
    r = reach(n, j)
    if j - r <= y < j: return 1
    if j < y <= j + r: return -1
    return 0

def irregular(N, p, f):
    bad = []
    for j in range(3, p + 1):
        for y in range(1, p + 1):
            if y != j and rel(N, f(j), f(y)) != rel(p, j, y):
                bad.append((j, y)); break
    return bad

def g_after(N, B, depth):
    # Theorem G (any centre) after <= depth valid steps; returns the steps or None
    B = set(B)
    if centre(N, B): return []
    if depth == 0: return None
    for m in range(1, N + 1):
        if valid(N, B, m):
            r = g_after(N, B | {m}, depth - 1)
            if r is not None: return [m] + r
    return None

maps = {
    'phi12': lambda y: 2 if y == 2 else 2 * y - 1,
    'phiE': lambda y: y if y <= 2 else 2 * y,
}
if __name__ == '__main__':
    name = sys.argv[1]; f = maps[name]
    for N in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
        for p in range(3, N):
            if all(1 <= f(y) <= N for y in range(1, p + 1)) and max(f(y) for y in range(1, p + 1)) >= N - 1:
                bad = irregular(N, p, f)
                img = {f(y) for y in range(1, p + 1)}
                st = g_after(N, img, 2) if not bad else None
                print(N, N % 4, p, 'irregular' if bad else 'regular', bad[:3], 'G-steps', st)
