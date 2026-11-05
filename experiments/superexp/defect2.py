"""Evens-first slips: first block F = E - {2k} + {2k+1}, second block S = O - {2k+1} + {2k}.
Prints the induced-system differences w.r.t. the n-strip (and the offsets of S given F)."""
import sys
from defect import induced

N = int(sys.argv[1]); n = N // 2
for k in range(1, n):
    E = set(range(2, N + 1, 2)); O = set(range(1, N + 1, 2))
    F = (E - {2 * k}) | {2 * k + 1}; S = (O - {2 * k + 1}) | {2 * k}
    dF, _ = induced(N, F); dS, oS = induced(N, S, F)
    print(k, "first", dF, "second", dS, oS)
