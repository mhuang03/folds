"""For N = 2^L: the order 'popcount(m-1) descending, then m ascending' is a full valid sequence.
Test its restriction to initial segments [1, k] (and to [N] minus an adjacent pair)."""
from lib import valid_seq

for L in range(2, 7):
    N = 1 << L
    seq = sorted(range(1, N + 1), key=lambda m: (-bin(m - 1).count('1'), m))
    print(N, 'full', valid_seq(N, seq))
    bad = [k for k in range(1, N + 1) if not valid_seq(N, [m for m in seq if m <= k])]
    print('   initial segments failing:', bad)
    badp = [r for r in range(1, N) if not valid_seq(N, [m for m in seq if m not in (r, r + 1)])]
    print('   adjacent pairs failing:', len(badp), 'of', N - 1)
