"""pieces.py FILE K [NMIN]: fit every (order type, sign matrix) class from pieces.c by a
quasi-polynomial and report its period, its degree and its leading coefficient."""
import sys
from collections import defaultdict
from fractions import Fraction as F
from math import factorial
import sympy as sp
from fit import try_period, x

fn, K = sys.argv[1], int(sys.argv[2])
nmin = int(sys.argv[3]) if len(sys.argv) > 3 else 1
npairs = K * (K - 1) // 2
nsig = 3 ** npairs
data = defaultdict(dict)
Ns = set()
for l in open(fn):
    n, key, c = map(int, l.split())
    data[key][n] = c
    Ns.add(n)
Ns = sorted(Ns)


def decode(key):
    code, s = divmod(key, nsig)
    # Lehmer code -> pattern
    digits = []
    for i in range(K):
        base = K - i
        digits.append(None)
    lehmer = []
    for i in reversed(range(K)):
        lehmer.append(code % (K - i))
        code //= (K - i)
    lehmer.reverse()
    avail = list(range(1, K + 1))
    pi = [avail.pop(r) for r in lehmer]
    sig = []
    for _ in range(npairs):
        sig.append(s % 3 - 1)
        s //= 3
    sig.reverse()
    pairs = [(i, j) for j in range(1, K) for i in range(j)]
    return pi, dict(zip(pairs, sig))


def sigstr(sig):
    return ' '.join(f's{i+1}{j+1}={"-0+"[v+1]}' for (i, j), v in sig.items())


tot = defaultdict(int)
rows = []
for key, d in data.items():
    full = {n: d.get(n, 0) for n in Ns}
    for n in Ns:
        tot[n] += full[n]
    for deg in range(0, K + 1):
        res = None
        for p in range(1, 49):
            res = try_period(full, deg, p, nmin)
            if res:
                break
        if res:
            break
    pi, sig = decode(key)
    if not res:
        rows.append((pi, sig, None, None, None))
        continue
    polys, checks = res
    lead = sp.Poly(polys[0], x).coeff_monomial(x ** deg) if deg else polys[0]
    rows.append((pi, sig, p, deg, lead))
    if K <= 3:
        print(''.join(map(str, pi)), sigstr(sig), {r: sp.factor(P) for r, P in polys.items()})
rows.sort(key=lambda r: (r[0], str(r[1])))
from math import lcm
per = 1
vol = 0
for pi, sig, p, deg, lead in rows:
    print('pattern', ''.join(map(str, pi)), sigstr(sig), ' period', p, ' degree', deg, ' lead', lead)
    if p:
        per = lcm(per, p)
        if deg == K:
            vol += lead
print(len(rows), 'nonempty classes; lcm of periods', per, '; sum of top-degree leading coeffs', vol)
