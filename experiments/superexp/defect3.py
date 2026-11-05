"""Single slips for odd N = 2n+1 (and even N), both block orders.
Slip k: 2k (even) and 2k+1 (odd) change blocks.  Prints the induced diffs."""
import sys
from defect import induced

N = int(sys.argv[1])
E = set(range(2, N + 1, 2)); O = set(range(1, N + 1, 2))
for k in range(1, (N + 1) // 2):
    if 2 * k + 1 > N:
        continue
    A = (E - {2 * k}) | {2 * k + 1}; B = (O - {2 * k + 1}) | {2 * k}
    for name, F, S in (("E-first", A, B), ("O-first", B, A)):
        dF, _ = induced(N, F); dS, oS = induced(N, S, F)
        print(k, name, len(F), "first", dF, "second", dS, oS)
