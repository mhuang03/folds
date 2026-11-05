"""Effective pair couplings inside the full system, from exact counts:
   J(m,m') = log[ a * a_{-m,m'} / (a_{-m} * a_{-m'}) ]
           = log[ P(C_m, C_m' | rest) / (P(C_m | rest, C_m' dropped) ...) ]  (conditional interaction).
Output droptwo.txt: N m m' J.  Uses ./dpx."""
import sys, os, subprocess, math
from wallis_exact import A

HERE = os.path.dirname(os.path.abspath(__file__))
fn = os.path.join(HERE, "droptwo.txt")


def cnt(N, *ps):
    return int(subprocess.check_output([os.path.join(HERE, "dpx"), str(N)] + [str(p) for p in ps]))


done = set()
if os.path.exists(fn):
    for line in open(fn):
        done.add(tuple(map(int, line.split()[:3])))
N0, N1 = int(sys.argv[1]), int(sys.argv[2])
with open(fn, "a") as f:
    for N in range(N0, N1 + 1):
        one = {m: cnt(N, m) for m in range(2, N)}
        for m in range(2, N):
            for mp in range(m + 1, N):
                # mirror symmetry: keep the lexicographically smaller representative
                a, b = sorted((N + 1 - mp, N + 1 - m))
                if (a, b) < (m, mp) or (N, m, mp) in done:
                    continue
                J = math.log(A[N - 1] * cnt(N, m, mp) / (one[m] * one[mp]))
                f.write("%d %d %d %.10f\n" % (N, m, mp, J))
        f.flush()
