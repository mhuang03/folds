"""qpoly.py K: exact quasi-polynomial of T(N,K) from classes_K.json, class by class.

Same mathematics as combine.py, but scales to large periods (K = 6: lcm = 104160):
each class GF t^s num(t)/prod(1-t^d) is turned into its own quasi-polynomial of period
p_c = lcm(d) (valid for all N >= 0 because deg(num)+s < sum(d), checked), from the values at
N = r + m p_c, m = 0..K (exact Newton interpolation in m, then substitution m = (N-r)/p_c).
Classes are summed within groups of equal period, then the groups are added (period lcm).

For each coefficient c_j(N) of T = sum_j c_j(N) N^j it prints the minimal period and the
exact-order Fourier components (c_j = sum_d g_d(N mod d), g_d with frequencies of exact
order d), and checks the total against the direct series expansion for N <= NCHECK.
Writes components_K.json (all components) and qpK_c<j>.txt for the nonconstant coefficients (residue, value) at their minimal period.
"""
import sys
import json
from fractions import Fraction as Fr
from math import lcm, comb

K = int(sys.argv[1])
NCHECK = int(sys.argv[2]) if len(sys.argv) > 2 else 400
L = [json.loads(l) for l in open(f'classes_{K}.json')]


def expand(c, n):
    a = [0] * n
    for i, v in enumerate(c['num']):
        if c['shift'] + i < n:
            a[c['shift'] + i] += v
    for d in c['den']:
        for i in range(d, n):
            a[i] += a[i - d]
    return a


def poly_mul_linear(p, a, b):
    """p(x) * (a + b x)"""
    out = [Fr(0)] * (len(p) + 1)
    for i, c in enumerate(p):
        out[i] += a * c
        out[i + 1] += b * c
    return out


def class_qp(c):
    p = lcm(*c['den'])
    assert len(c['num']) - 1 + c['shift'] < sum(c['den'])
    vals = expand(c, (K + 1) * p)
    Q = []
    for r in range(p):
        ys = [vals[r + m * p] for m in range(K + 1)]
        # Newton forward differences in m: f(m) = sum_k D_k C(m, k)
        D = []
        cur = ys[:]
        for k in range(K + 1):
            D.append(cur[0])
            cur = [cur[i + 1] - cur[i] for i in range(len(cur) - 1)]
        # C(m,k) with m = (N - r)/p, as polynomial in N
        poly = [Fr(0)] * (K + 1)
        basis = [Fr(1)]
        for k in range(K + 1):
            for i, v in enumerate(basis):
                poly[i] += D[k] * v
            # basis *= (m - k)/(k+1),  m - k = (N - r - k p)/p
            basis = poly_mul_linear(basis, Fr(-r - k * p, p * (k + 1)), Fr(1, p * (k + 1)))
        Q.append(poly[:K + 1])
    return p, Q


groups = {}
for idx, c in enumerate(L):
    p, Q = class_qp(c)
    if p not in groups:
        groups[p] = [[Fr(0)] * (K + 1) for _ in range(p)]
    G = groups[p]
    for r in range(p):
        for j in range(K + 1):
            G[r][j] += Q[r][j]
print('class periods:', {p: sum(1 for c in L if lcm(*c['den']) == p) for p in sorted(groups)},
      flush=True)

P = lcm(*groups)
print('total period bound', P, flush=True)

coef = []
for j in range(K + 1):
    parts = [(p, [G[r][j] for r in range(p)]) for p, G in groups.items()]
    # minimal period of each part and of the total
    coef.append(parts)


def value(N):
    return sum(sum(g[N % p] for p, g in coef[j]) * N**j for j in range(K + 1))


ser = [0] * (NCHECK + 1)
for c in L:
    e = expand(c, NCHECK + 1)
    for i in range(NCHECK + 1):
        ser[i] += e[i]
for N in range(NCHECK + 1):
    assert value(N) == ser[N], N
print(f'quasi-polynomial = series for N = 0..{NCHECK}')
with open(f'T{K}_series.txt', 'w') as f:
    for n in range(1, NCHECK + 1):
        f.write(f'{n} {ser[n]}\n')


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def mobius(n):
    m, q, r = n, 2, 1
    while q * q <= m:
        if m % q == 0:
            m //= q
            if m % q == 0:
                return 0
            r = -r
        q += 1
    return -r if m > 1 else r


def components(parts):
    """exact-order Fourier components of sum of periodic parts; each part decomposes on the
    divisors of its own period, so we decompose the parts and add."""
    out = {}
    for p, f in parts:
        avg = {d: [sum(f[r::d], Fr(0)) / (p // d) for r in range(d)] for d in divisors(p)}
        for d in divisors(p):
            g = [Fr(0)] * d
            for e in divisors(d):
                mu = mobius(d // e)
                if mu:
                    for r in range(d):
                        g[r] += mu * avg[e][r % e]
            if d in out:
                out[d] = [a + b for a, b in zip(out[d], g)]
            else:
                out[d] = g
    return {d: g for d, g in out.items() if any(g)}


summary = []
dump = {}
for j in range(K, -1, -1):
    comp = components(coef[j])
    dump[j] = {d: [str(x) for x in g] for d, g in comp.items()}
    per = lcm(*comp) if comp else 1
    print(f'c_{j}: minimal period {per}; exact-order components d = {sorted(comp)}', flush=True)
    summary.append((j, per, comp))
    if per == 1:
        print('      constant', comp.get(1, [0])[0])
    else:
        vals = [sum(g[r % d] for d, g in comp.items()) for r in range(per)]
        with open(f'qp{K}_c{j}.txt', 'w') as f:
            f.write(f'# c_{j}(N) of T(N,{K}) for N mod {per}\n')
            for r, v in enumerate(vals):
                f.write(f'{r} {v}\n')
        for d, g in sorted(comp.items()):
            if d <= 16:
                print(f'      d={d}:', ' '.join(str(x) for x in g))
            else:
                print(f'      d={d}: (length {d}, denominators lcm', lcm(*[x.denominator for x in g]), ')')

with open(f'components_{K}.json', 'w') as f:
    json.dump(dump, f)
