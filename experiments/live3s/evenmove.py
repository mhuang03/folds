# evenmove.py N0 N1: even N = 2p, even c: phi12 into [2p] with the panel g moved to c
# (g = c/2 or (c+2)/2); regular outside {1, 2, g}?  Theorem G for the image after <= 1 step?
import sys
from base import *
from moved import regular_except
from maps import g_after
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
    p = N // 2
    row = []
    for c in range(6, N + 1, 2):
        res = []
        for g in (c // 2, (c + 2) // 2):
            if not (3 <= g <= p): continue
            f = lambda y, g=g: c if y == g else (2 if y == 2 else 2 * y - 1)
            if regular_except(N, p, f, {1, 2, g}): continue
            img = {f(y) for y in range(1, p + 1)}
            res.append((g, g_after(N, img, 1)))
        row.append((c, res))
    print(N, row)
