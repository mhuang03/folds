# Fraction of random N in [X, 2X] covered with M = 2^j in [N^theta, sqrt N] (exponent ~theta/6),
# using only PROVEN instances of H (coverage_lib.H).
# python3 coverage3.py theta samples X1 X2 ...
import sys, random
from coverage_lib import H
th = float(sys.argv[1]); S = int(sys.argv[2]); random.seed(2)
for X in (int(float(a)) for a in sys.argv[3:]):
    ok = 0
    for _ in range(S):
        N = random.randrange(X, 2 * X); found = False; M = 1
        while M * (M + 1) <= N and not found:
            if M >= N ** th:
                for q in range(N // (M + 1) + 1, N // M + 1):
                    r = N - q * M
                    if H(q, r): found = True; break
            M *= 2
        ok += found
    print(f"X={X:.1e} theta={th}: covered {ok}/{S}", flush=True)
