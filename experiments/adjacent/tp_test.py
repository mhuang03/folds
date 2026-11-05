"""Two-phase greedy (peel2.py) on the 2-sets that Cov3 misses."""
import sys
from peel2 import two_phase

N = int(sys.argv[1])
pairs = eval(sys.argv[2])
for (u, v) in pairs:
    A = two_phase(N, u, v)
    print((u, v), 'found' if A else 'no', sorted(A) if A else '')
