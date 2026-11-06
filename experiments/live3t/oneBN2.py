# oneBN2.py NMAX: the exact rule of Live3t.coReach_one_b_N, checked for N = 2 mod 4, N <= NMAX:
# N = 4s + 2, p = 2s + 2, zA(k) = 2k - 1 (k <= s + 1), 2k - 2 (k >= s + 2); for 2 <= j <= s + 1,
# e in {0, 1}: the map zA with j -> 2j - 1 - e is increasing, regular outside {1, j, p}, the
# preimage {1, j, p} is valid and not dead in [p], and the image satisfies Theorem G with the
# centre 1/2.  Then {1, b, N} for 2 <= b <= 2s + 1 (j = b/2 + 1, e = (b + 1) mod 2), and the
# mirror images b >= 2s + 2.
import sys
from nb import *
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
bad = []
for N in range(14, NMAX + 1, 4):
    s = N // 4; p = 2 * s + 2
    zA = lambda k: 2 * k - 1 if k <= s + 1 else 2 * k - 2
    assert [zA(k) for k in range(1, p + 1)] == [(k * (N + 2)) // (p + 1) for k in range(1, p + 1)]
    for j in range(2, s + 2):
        for e in (0, 1):
            phi = lambda k: 2 * j - 1 - e if k == j else zA(k)
            img = {phi(k) for k in range(1, p + 1)}
            ok = (increasing(N, p, phi) and set(irregular(N, p, phi)) <= {1, j, p} and
                  valid3(p, 1, j, p) and not dead3(p, 1, j, p) and inward1(N, img))
            if not ok: bad.append((N, j, e))
print('failures:', bad)
