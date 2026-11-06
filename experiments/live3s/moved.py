# moved.py NMAX: the near copies phi12 / phiE with the third panel g moved by one.
#   N = 2p - 1, p odd (N = 1 mod 4): phi12, c even, g even, c = 2g (c = 0 mod 4) or
#       c = 2g - 2 (c = 2 mod 4)
#   N = 2p + 1, p odd (N = 3 mod 4): phiE, c odd, g odd, c = 2g - 1 (c = 1 mod 4) or
#       c = 2g + 1 (c = 3 mod 4)
# Check: regular at every j not in {1, 2, g} (for all y), and the image satisfies Theorem G
# after at most DEPTH valid steps (search); print the failures and the steps used.
import sys
from base import *
from maps import rel, g_after

def regular_except(N, p, f, exc):
    for j in range(1, p + 1):
        if j in exc: continue
        for y in range(1, p + 1):
            if y != j and rel(N, f(j), f(y)) != rel(p, j, y): return (j, y)
    return None

def maps_for(N, c):
    if N % 4 == 1 and c % 2 == 0:
        p = (N + 1) // 2
        g = c // 2 if c % 4 == 0 else (c + 2) // 2
        base = lambda y: 2 if y == 2 else 2 * y - 1
    elif N % 4 == 3 and c % 2 == 1:
        p = (N - 1) // 2
        g = (c + 1) // 2 if c % 4 == 1 else (c - 1) // 2
        base = lambda y: y if y <= 2 else 2 * y
    else:
        return None
    f = lambda y: c if y == g else base(y)
    return p, g, f

if __name__ == '__main__':
    N0, N1, D = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for N in range(N0, N1 + 1):
        res = []
        for c in range(6, N - 1):
            r = maps_for(N, c)
            if r is None: continue
            p, g, f = r
            if not (3 <= g <= p - 2): res.append((c, 'g out')); continue
            bad = regular_except(N, p, f, {1, 2, g})
            img = {f(y) for y in range(1, p + 1)}
            st = g_after(N, img, D)
            res.append((c, 'irr%s' % (bad,) if bad else 'ok', st))
        print(N, res)
