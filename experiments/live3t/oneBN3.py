# oneBN3.py NMAX: {1, b, N} for N = 4 mod 8 through Z(N, N/2 + 2) (k -> 2k - 1 for
# 4k <= N + 6, 2k - 2 above) with the panel j of b moved by e in {0, -1}: checks, for
# 2 <= b <= N/2 + 1 (the rest by the mirror), regularity outside {1, j, p}, the preimage, and
# Theorem G with the centre 1/2 for the image.
import sys
from nb import *
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
for N in range(52, NMAX + 1, 8):
    p = N // 2 + 2
    Z = lambda k: (k * (N + 2)) // (p + 1)
    t = (N + 6) // 4
    pass  # assert all(Z(k) == (2 * k - 1 if k <= t else 2 * k - 2) for k in range(1, p + 1))
    fails = []
    for b in range(2, N // 2 + 2):
        ok = False
        for j in range(2, p):
            for e in (0, -1, 1):
                if Z(j) + e != b: continue
                phi = lambda k: Z(k) + (e if k == j else 0)
                img = {phi(k) for k in range(1, p + 1)}
                if (increasing(N, p, phi) and set(irregular(N, p, phi)) <= {1, j, p} and
                        valid3(p, 1, j, p) and not dead3(p, 1, j, p) and inward1(N, img)):
                    ok = (j, e); break
            if ok: break
        if not ok: fails.append(b)
    print('N=%d p=%d t=%d failures %s' % (N, p, t, fails))
