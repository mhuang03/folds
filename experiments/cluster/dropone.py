"""Conditional single-site factors from exact counts with one constraint removed:
   u_m(N) = log( a(N) / a_{-m}(N) ) - log w(r_m) = log [ P(C_m | all other C) / w(r_m) ].
Output dropone.txt: N m r u_m.  Uses ./dpx (exact subset DP)."""
import sys, os, subprocess, math
from wallis_exact import logw, A

HERE = os.path.dirname(os.path.abspath(__file__))
fn = os.path.join(HERE, "dropone.txt")
done = set()
if os.path.exists(fn):
    for line in open(fn):
        N, m = map(int, line.split()[:2])
        done.add((N, m))
N0, N1 = int(sys.argv[1]), int(sys.argv[2])
with open(fn, "a") as f:
    for N in range(N0, N1 + 1):
        for m in range(2, (N + 1) // 2 + 1):     # mirror symmetry: left half + middle
            if (N, m) in done:
                continue
            r = min(m - 1, N - m)
            c = int(subprocess.check_output([os.path.join(HERE, "dpx"), str(N), str(m)]))
            u = math.log(A[N - 1] / c) - logw(r)
            f.write("%d %d %d %.10f\n" % (N, m, r, u))
            f.flush()
