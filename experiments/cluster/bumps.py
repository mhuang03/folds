"""Local bumps b(N) = f(N) - (f(N-2) + f(N+2))/2 for y = log(a/aW) and for pair sums."""
import math
from wallis_exact import log_aW, A
from pairsum import kdata

y = {N: math.log(A[N - 1]) - log_aW(N) for N in range(1, len(A) + 1)}


def bump(f, N):
    return f[N] - (f[N - 2] + f[N + 2]) / 2


S2 = {}
for N in range(3, 34):
    S2[N] = sum(math.log1p(k) for (m, mp, r, rp, p, k) in kdata(N))
print(" N  N%3  b(y)     b(S2)    b(y-S2)")
for N in range(5, 32):
    d = {n: y[n] - S2[n] for n in S2}
    print("%2d  %d  %8.4f %8.4f %8.4f" % (N, N % 3, bump(y, N), bump(S2, N), bump(d, N)))
