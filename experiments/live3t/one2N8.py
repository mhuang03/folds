# one2N8.py NMAX: {1, 2, N} for N = 8t + 4 through Z(N, N/2 + 2) in closed form
#   zB t k = 2k - 1 - [k > t + 1] - [k > 2t + 2] - [k > 3t + 3],  p = 4t + 4,
# with the panel 2 moved from 3 to 2: regular outside {1, 2, p}, {1, 2, p} valid and not dead
# in [p], and the image satisfies Theorem G with the centre 1/2.  (The rule of
# Live3t.coReach_one_two_N8.)
import sys
from nb import *
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
bad = []
for N in range(12, NMAX + 1, 8):
    t = (N - 4) // 8; p = 4 * t + 4
    zB = lambda k: 2 * k - 1 - (k > t + 1) - (k > 2 * t + 2) - (k > 3 * t + 3)
    assert all(zB(k) == (k * (N + 2)) // (p + 1) for k in range(1, p + 1))
    phi = lambda k: 2 if k == 2 else zB(k)
    img = {phi(k) for k in range(1, p + 1)}
    ok = (increasing(N, p, phi) and set(irregular(N, p, phi)) <= {1, 2, p} and
          valid3(p, 1, 2, p) and not dead3(p, 1, 2, p) and inward1(N, img) and phi(p) == N)
    if not ok: bad.append((N, irregular(N, p, phi), inward1(N, img)))
print('failures:', bad)
