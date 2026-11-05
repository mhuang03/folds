"""Is there a single aggregated certificate sum_m w(m) D_m(c) > 0 (w >= 0) for all labellings c
with t labels?  By LP duality this fails iff some probability distribution p over labellings has
E_p[D_m] <= 0 for all m, D_m(c) = #{L(m): c <= c(m)} - #{R(m): c < c(m)}.
usage: lpdist.py N t     (brute force over t^N labellings, small N only)"""
import itertools, numpy as np, sys
from scipy.optimize import linprog
N, t = int(sys.argv[1]), int(sys.argv[2])
def D(c):
    out = []
    for m in range(N):
        r = min(m, N - 1 - m); v = c[m]
        out.append(sum(c[x] <= v for x in range(m - r, m)) - sum(c[x] < v for x in range(m + 1, m + r + 1)))
    return out
labs = list(itertools.product(range(t), repeat=N))
A = np.array([D(c) for c in labs]).T
K = len(labs)
res = linprog(np.zeros(K), A_ub=A, b_ub=np.zeros(N), A_eq=np.ones((1, K)), b_eq=[1], bounds=(0, None), method='highs')
print(N, t, 'distribution exists (no aggregated certificate)' if res.status == 0 else 'no distribution: aggregated certificate exists')
if res.status == 0:
    p = res.x
    for i in np.nonzero(p > 1e-9)[0]:
        print(''.join(map(str, labs[i])), round(p[i], 4), D(labs[i]))
else:
    # find the certificate w
    res2 = linprog(np.zeros(N), A_ub=-A.T, b_ub=-np.ones(K), bounds=(0, None), method='highs')
    print('w =', np.round(res2.x, 4) if res2.status == 0 else res2.message)
