# thresh.py lo hi: smallest nu <= q/2 (and smallest q - nu for nu > q/2) without a
# parity-tree GoodL(q, nu) order (None = all exist).
import sys
from ptree import solve
lo, hi = int(sys.argv[1]), int(sys.argv[2])
for q in range(lo, hi + 1):
    f = None
    for nu in range(0, q // 2 + 1):
        if not solve(q, nu):
            f = nu
            break
    g = None
    for nu in range(q - 1, q // 2, -1):
        if not solve(q, nu):
            g = q - nu
            break
    print(q, f, g, flush=True)
