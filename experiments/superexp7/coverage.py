# Which N admit the SuperExp6 all-N composition (class sizes M = 2^j and M+1) with a
# PROVEN instance of H?  Proven H (Lean, Folds/SuperExp7.lean + Live4):
#   rho in {0, 1, q-1};  q 23-smooth (every rho);  block composition q = m j.
# Usage: python3 coverage.py NMAX [C]   (M ranges over powers of 2 with M >= sqrt(N)/C)
import sys, math
NMAX = int(sys.argv[1]); C = float(sys.argv[2]) if len(sys.argv) > 2 else 4.0

from coverage_lib import H

ok = 0; tot = 0; bad = []
for N in range(64, NMAX + 1):
    tot += 1
    found = False
    M = 1
    while M * (M + 1) <= N:
        if M >= math.sqrt(N) / C:
            lo = N // (M + 1) + 1; hi = N // M
            for q in range(lo, hi + 1):
                r = N - q * M
                if 0 <= r < q and H(q, r): found = True; break
        if found: break
        M *= 2
    if found: ok += 1
    elif len(bad) < 20: bad.append(N)
print(f"N in [64,{NMAX}], C={C}: covered {ok}/{tot} = {ok/tot:.4f}; first uncovered {bad}")
