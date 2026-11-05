"""min over valid a of LDS / LIS of the restriction of a to the value interval [1, n]."""
from common import *
import sys
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N)
    mL = [99] * (N + 1); mI = [99] * (N + 1)
    for a in A:
        a = list(a)
        for n in range(1, N + 1):
            b = [x for x in a if x <= n]
            mL[n] = min(mL[n], lds(b)); mI[n] = min(mI[n], lis(b))
    print(N, 'LDS[1..n]:', mL[1:], ' LIS[1..n]:', mI[1:])
