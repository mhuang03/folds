"""List the sets D of [N] of size <= k that are NOT co-reachable ([N] \\ D not reachable)."""
import sys
from itertools import combinations
from lib import reachable

N = int(sys.argv[1])
k = int(sys.argv[2])
full = set(range(1, N + 1))
for size in range(1, k + 1):
    bad = [D for D in combinations(range(1, N + 1), size) if not reachable(N, full - set(D))]
    print(size, len(bad))
    for D in bad:
        print('  ', D)
