"""The first-panel law F(N,m)/a(N) (= last-panel law, by reversal).
Heuristic (independence / Wallis model): the last panel's own constraint is automatically
satisfied (its window is full), so P(last = m) is proportional to 1/w(r_m), with
w(r) = 4^r r!^2/(2r+1)!  ~  sqrt(pi/(4r)).  Continuum limit: density proportional to
sqrt(min(x,1-x)), whose variance is 1/17.5 = 0.057143.
Compare the exact law with this prediction, and fit the limiting variance."""
import math
import numpy as np
from common import stats


def w(r):
    return math.exp(r * math.log(4) + 2 * math.lgamma(r + 1) - math.lgamma(2 * r + 2))


rule = 'semi'
print('N   Var/N^2   Var_W/N^2  (Var - Var_W)/N^-1 terms   max |N F/a - N P_W| (bulk)   TV distance')
for n in range(8, 31):
    d = stats(n, rule)
    F = np.array(d['F'], dtype=float); A = F.sum()
    p = F / A
    q = np.array([1 / w(min(m - 1, n - m)) for m in range(1, n + 1)]); q /= q.sum()
    mu = (n + 1) / 2
    v = sum(p[m - 1] * (m - mu) ** 2 for m in range(1, n + 1)) / n**2
    vw = sum(q[m - 1] * (m - mu) ** 2 for m in range(1, n + 1)) / n**2
    tv = 0.5 * np.abs(p - q).sum()
    print(f'{n:2d} {v:.5f}  {vw:.5f}   {n*(v-vw):+.4f}   TV={tv:.4f}')
n = 30
d = stats(n, rule)
F = np.array(d['F'], dtype=float); p = F / F.sum()
q = np.array([1 / w(min(m - 1, n - m)) for m in range(1, n + 1)]); q /= q.sum()
print('\nN = 30: m, N*P(first=m), N*P_W(m), ratio')
for m in range(1, n // 2 + 1):
    print(f'{m:2d} {n*p[m-1]:.4f} {n*q[m-1]:.4f} {p[m-1]/q[m-1]:.3f}')
# boundary columns: F(N,m)/F(N,1) for fixed m
print('\nF(N,m)/F(N,1), m = 2..6')
for n in range(12, 31):
    d = stats(n, rule)
    print(n, ' '.join(f'{d["F"][m-1]/d["F"][0]:.3f}' for m in range(2, 7)))
print('\nN*F(N,1)/a(N) * (ln N), * N^0.5 : boundary decay')
for n in range(12, 31):
    d = stats(n, rule)
    x = n * d['F'][0] / d['total']
    print(n, f'{x:.4f} {x*math.log(n):.4f} {x*math.sqrt(n):.4f}')
