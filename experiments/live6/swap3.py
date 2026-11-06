"""swap3.py NMAX CMAX: check the claim
   p odd >= 3, h in {0, 1}, c >= 2, N >= (c + 2) p + 1  ==>  Swap(N, p, h, c) is an inward copy
and report, for p odd, the exact set of N where it holds (to see sharpness)."""
import sys
from swap import swapped
from twoside import is_inward_copy

NMAX, CMAX = int(sys.argv[1]), int(sys.argv[2])
bad = 0
for c in range(2, CMAX + 1):
    for p in range(3, NMAX // (c + 2) + 1, 2):
        for h in (0, 1):
            for N in range((c + 2) * p + 1, NMAX + 1):
                if not is_inward_copy(N, swapped(N, p, h, c)):
                    bad += 1
                    print('FAIL', c, p, h, N)
            # below the bound
            below = [N for N in range(2 * p + h, (c + 2) * p + 1)
                     if swapped(N, p, h, c)[-2] < N - c and is_inward_copy(N, swapped(N, p, h, c))]
            if below:
                print('also holds below bound', c, p, h, below)
print('failures', bad)
