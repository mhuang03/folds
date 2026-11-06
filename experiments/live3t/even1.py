# even1.py NMAX: {1, 2, c}, N = 1 mod 4, c even, through phi12 (N = 2p - 1, 1 -> 1, 2 -> 2,
# y -> 2y - 1) with the panel g = (c + 2)/2 sent to c (Live3r's rcov hints): for which c is the
# map regular outside {2, g} and the image inward (centre 1/2) after the steps
#   c = 2 mod 4: 4, 3, c + 2, (N + 3)/2        c = 0 mod 4: 4, 3, (N + 7)/2
# Prints per N the range of c that works, and MISMATCH if the c = 2 mod 4 set is not exactly
#   (N + 7)/2 <= c, 4c <= 3N + 9.
import sys
from nb import *
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
for N in range(53, NMAX + 1, 4):
    p = (N + 1) // 2
    res = {0: [], 2: []}
    for c in range(8, N - 1, 2):
        g = (c + 2) // 2
        phi = lambda y: 2 if y == 2 else (c if y == g else 2 * y - 1)
        if not increasing(N, p, phi) or not set(irregular(N, p, phi)) <= {1, 2, g}: continue
        img = {phi(y) for y in range(1, p + 1)}
        ms = [4, 3, c + 2, (N + 3) // 2] if c % 4 == 2 else [4, 3, (N + 7) // 2]
        if steps_ok(N, img, ms, 1): res[c % 4].append(c)
    def rng(l):
        # maximal initial run of consecutive members (step 4)
        out = [];
        for c in l:
            if out and c != out[-1] + 4: break
            out.append(c)
        return (out[0], out[-1], len(l) - len(out)) if out else None
    pred = [c for c in range(8, N - 1) if c % 4 == 2 and 2 * c >= N + 7 and 4 * c <= 3 * N + 9]
    if sorted(res[2]) != pred: print("MISMATCH", N, sorted(res[2]), pred)
    print('N=%d c=2 mod 4: %s; c=0 mod 4: %s' % (N, rng(res[2]), rng(res[0])))
