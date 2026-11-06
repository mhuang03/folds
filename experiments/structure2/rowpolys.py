"""Row generating functions: F_N(t) = sum_m F(N,m) t^(m-1), T_N(t) = sum_k T(N,k) t^k,
R_N(t) = sum_k reach(N,k) t^k.  Real-rootedness, unimodality, log-concavity, and the values at
t = -1 (alternating sums)."""
import numpy as np
from common import stats


def props(c):
    c = [float(x) for x in c]
    while c and c[-1] == 0:
        c.pop()
    r = np.roots(c[::-1]) if len(c) > 1 else []
    real = all(abs(z.imag) < 1e-6 * max(1, abs(z)) for z in r)
    lc = all(c[i] ** 2 >= c[i - 1] * c[i + 1] for i in range(1, len(c) - 1))
    k = int(np.argmax(c))
    um = all(c[i] <= c[i + 1] for i in range(k)) and all(c[i] >= c[i + 1] for i in range(k, len(c) - 1))
    return real, lc, um


for rule, Nmax in (('semi', 30), ('sym', 28)):
    print(rule)
    for n in range(4, Nmax + 1):
        d = stats(n, rule)
        F = d['F']; T = d['prefixes']; R = d['reach']
        pf, pt, pr = props(F), props(T), props(R)
        alt = lambda v: sum((-1) ** i * x for i, x in enumerate(v))
        print(f' {n:2d} F: real={pf[0]!s:5} lc={pf[1]!s:5} unimodal={pf[2]!s:5} | '
              f'T: real={pt[0]!s:5} lc={pt[1]!s:5} | R: real={pr[0]!s:5} lc={pr[1]!s:5} '
              f'R(-1)={alt(R)} T(-1)={alt(T)}')
