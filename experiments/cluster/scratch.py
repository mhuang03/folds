import mpmath as mp
from wallis_exact import log_aW_mp
mp.mp.dps = 40
# Richardson extrapolation of g(N) = log aW - (N/2)log(pi N/(2e)) - 1/4 log N  (even N)
def g(N):
    return log_aW_mp(N) - mp.mpf(N) / 2 * mp.log(mp.pi * N / (2 * mp.e)) - mp.log(N) / 4
Ns = [2 * 10**k for k in range(3, 9)]
vals = [g(N) for N in Ns]
# assume g = c0 + c1/N + c2/N^2: Richardson with ratio 10
r1 = [(10 * vals[i + 1] - vals[i]) / 9 for i in range(len(vals) - 1)]
r2 = [(100 * r1[i + 1] - r1[i]) / 99 for i in range(len(r1) - 1)]
print([mp.nstr(x, 20) for x in r2])
c = r2[-1]
print("c1 estimate", mp.nstr((vals[-1] - c) * Ns[-1], 10))
z = mp.zeta(-1, derivative=1)
print(mp.pslq([c, 1, mp.log(2), mp.log(mp.pi), z], maxcoeff=200, maxsteps=10**6))
