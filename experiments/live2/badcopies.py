"""badcopies.py N1 N2: window copies X of [N] whose complement is NOT reachable."""
import sys
from lib import load_copies

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for X, g in load_copies(N):
        if not g:
            print(N, X)
