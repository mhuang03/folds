"""swapcheck.py NMAX: verify the SWAP LEMMA for all N <= NMAX:
   p odd >= 3, h in {0, 1}, c >= 2, N + h >= 2cp + 1  ==>
   Swap(N, p, h, c) = X(N, p, h) with its last element N - h moved to N - c
   is a window copy (I = 0 on it) and inward with the centre at N - c
   (I <= 0 left of N - c, I >= 0 right of it)."""
import sys
from swap import swapped
from twoside import imb_all

NMAX = int(sys.argv[1])
cnt = bad = 0
for N in range(1, NMAX + 1):
    for p in range(3, N + 1, 2):
        for h in (0, 1):
            for c in range(2, N):
                if N + h < 2 * c * p + 1:
                    break
                X = swapped(N, p, h, c)
                ind, I = imb_all(N, X)
                ok = all((I[m] == 0) if ind[m] else (I[m] <= 0 if m < N - c else I[m] >= 0)
                         for m in range(1, N + 1))
                cnt += 1
                if not ok:
                    bad += 1
                    print('FAIL', N, p, h, c)
print('checked', cnt, 'failures', bad)
