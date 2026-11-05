"""Effective couplings J(m, m') (see droptwo.py) along the doubling diagonal m' in {2m-1, 2m, 2m+1}.
The doubling 2-cycle {N/3, 2N/3} (and its mirror {N/3+1, 2N/3+1}) sits on this diagonal where
also 2m' - N ~ m.  Prints, for each N, the profile and the sum over the near-2-cycle pairs
(pairs with |m' - 2m| <= 1 and |2m' - N - m| <= 1)."""
import sys, os, subprocess, math
from wallis_exact import A

HERE = os.path.dirname(os.path.abspath(__file__))
fn = os.path.join(HERE, "droptwo.txt")
d = {}
for line in open(fn):
    N, m, mp, J = line.split()
    d[(int(N), int(m), int(mp))] = float(J)


def cnt(N, *ps):
    return int(subprocess.check_output([os.path.join(HERE, "dpx"), str(N)] + [str(p) for p in ps]))


def J(N, m, mp):
    a, b = sorted((N + 1 - mp, N + 1 - m))
    for key in ((N, m, mp), (N, a, b)):
        if key in d:
            return d[key]
    v = math.log(A[N - 1] * cnt(N, m, mp) / (cnt(N, m) * cnt(N, mp)))
    d[(N, m, mp)] = v
    with open(fn, "a") as f:
        f.write("%d %d %d %.10f\n" % (N, m, mp, v))
    return v


N0, N1 = int(sys.argv[1]), int(sys.argv[2])
for N in range(N0, N1 + 1):
    near = []
    prof = []
    for m in range(2, N):
        for mp in (2 * m - 1, 2 * m, 2 * m + 1):
            if m < mp < N:
                if abs(2 * mp - N - m) <= 1:
                    near.append((m, mp, J(N, m, mp)))
    tot = sum(x[2] for x in near)
    print("N=%2d N%%3=%d  near-2-cycle pairs: %s  sum=%.3f" % (
        N, N % 3, " ".join("(%d,%d):%.3f" % x for x in near), tot), flush=True)
