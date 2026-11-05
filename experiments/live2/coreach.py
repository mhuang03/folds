"""coreach.py N1 N2: co-reachable 2-sets D = {u < v} ([N] \\ D reachable from scratch).
Prints, per N, the 2-sets that are NOT co-reachable, and which adjacent pairs {r, r+1} are."""
import sys
from lib import reachable

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    full = set(range(1, N + 1))
    bad = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1)
           if not reachable(N, full - {u, v})]
    adj = [r for r in range(1, N) if reachable(N, full - {r, r + 1})]
    print(N, 'not co-reachable:', bad, '| adjacent co-reachable r:', adj)
