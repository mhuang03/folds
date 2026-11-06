"""obstruction.py -- sets with huge discrepancy and huge imbalance field that still have a
constant fraction of valid moves (PROOFS.txt Prop. 2.5).

S = Beatty set of slope r1 on [1, N/2] and slope r2 on (N/2, N] (panel y in S iff
floor(r y) > floor(r (y-1)) inside each half).  For r1 != r2 the discrepancy is ~ |r1-r2| N/4 and
J is of order N on the middle half of the strip, but J takes only O(1) values on the outer
quarters, so V(S)/(N - |S|) stays bounded below.
"""
import math, sys


def stats(N, S):
    s = len(S)
    inS = [0] * (N + 2)
    for x in S: inS[x] = 1
    P = [0] * (N + 1)
    for y in range(1, N + 1): P[y] = P[y - 1] + inS[y]
    def Pt(y): return P[y % N] + (y // N) * s
    J = [None] + [Pt(2 * m - 1) - 2 * P[m - 1] for m in range(1, N + 1)]
    free = [m for m in range(1, N + 1) if not inS[m]]
    V = sum(1 for m in free if J[m] == 0)
    disc = max(abs(P[y] - s * y / N) for y in range(N + 1))
    rms = math.sqrt(sum(J[m] ** 2 for m in range(1, N + 1)) / N)
    return s, V, len(free), disc, rms


for N in [400, 1000, 4000, 10000]:
    for r1, r2 in [(0.5, 0.5), (0.4, 0.2), (0.6, 0.3), (0.5, 0.25)]:
        h = N // 2
        S = [y for y in range(1, h + 1) if math.floor(r1 * y) > math.floor(r1 * (y - 1))]
        S += [y for y in range(h + 1, N + 1) if math.floor(r2 * (y - h)) > math.floor(r2 * (y - h - 1))]
        s, V, f, disc, rms = stats(N, S)
        print("N=%5d r1=%.2f r2=%.2f |S|=%5d  V/(N-|S|)=%.3f  disc=%7.1f  rms J=%8.1f" % (N, r1, r2, s, V / f, disc, rms))
