# oneBN.py NMAX: the family {1, b, N}, N even, through the centred Beatty copy Z(N, N/2 + 1)
# (closed form 2k - 1 for 4k <= N + 4, 2k - 2 above) with the panel of b moved by one if b is
# not in the image.  Checks for every even N <= NMAX and every 2 <= b <= N - 1:
#   regularity outside the preimage {1, j, p}, validity / non-deadness of the preimage, and
#   Theorem G for the image (which centre), reporting the b that fail.
import sys
from nb import *
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200

def Z(N, k): return 2 * k - 1 if 4 * k <= N + 4 else 2 * k - 2

def centres(N, S):
    """the centres c2 (as 2 * centre) for which Theorem G holds"""
    out = []
    for c2 in range(1, 2 * N + 2):
        ok = True
        for m in range(1, N + 1):
            if m in S: continue
            l, r = L(N, S, m), R(N, S, m)
            if 2 * m == c2 or (2 * m < c2 and l > r) or (2 * m > c2 and r > l): ok = False; break
        if ok: out.append(c2)
    return out

for N in range(52, NMAX + 1, 2):
    p = N // 2 + 1
    base = [Z(N, k) for k in range(1, p + 1)]
    assert base[0] == 1 and base[-1] == N and base == [(k * (N + 2)) // (p + 1) for k in range(1, p + 1)]
    fails = []; info = {}
    for b in range(2, N):
        best = None
        for j in range(2, p):
            for e in (0, 1, -1):
                if base[j - 1] + e != b: continue
                phi = lambda y: base[y - 1] + (e if y == j else 0)
                if not increasing(N, p, phi): continue
                if not set(irregular(N, p, phi)) <= {1, j, p}: continue
                if not valid3(p, 1, j, p) or dead3(p, 1, j, p): continue
                img = {phi(y) for y in range(1, p + 1)}
                cs = centres(N, img)
                if cs: best = (j, e, cs[0], cs[-1]); break
            if best: break
        if best: info[b] = best
        else: fails.append(b)
    # summary: for which b is the centre not 1
    odd = sorted(set((b % 4, info[b][1], info[b][2] == 1) for b in info))
    print('N=%d fails %s; (b mod 4, move, centre 1/2 ok):' % (N, fails), odd)
    sys.stdout.flush()
