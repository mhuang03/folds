# Sampled version of coverage.py for large N: fraction of random N in [X, 2X] covered with
# M = 2^j >= sqrt(N)/C.   python3 coverage2.py C samples X1 X2 ...
import sys, math, random
sys.setrecursionlimit(10000)
from coverage_lib import H
C = float(sys.argv[1]); S = int(sys.argv[2])
random.seed(1)
for X in (int(float(a)) for a in sys.argv[3:]):
    ok = 0
    for _ in range(S):
        N = random.randrange(X, 2 * X); found = False; M = 1
        while M * (M + 1) <= N and not found:
            if M >= math.sqrt(N) / C:
                for q in range(N // (M + 1) + 1, N // M + 1):
                    r = N - q * M
                    if 0 <= r < q and H(q, r): found = True; break
            M *= 2
        ok += found
    print(f"X={X:.1e} C={C}: covered {ok}/{S}", flush=True)
