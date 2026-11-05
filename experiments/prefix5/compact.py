"""compact.py K: compact form of the exact quasi-polynomial T(N,K) from components_K.json.

Each coefficient c_j(N) is a sum of exact-order components g_d(N mod d).  We group them by
the prime p in {5, 7, 31} dividing d (no d is divisible by two of them), the rest being the
{2,3}-part, so that
     c_j(N) = A_j(N mod a_j) + B_j(N mod b_j) + C_j(N mod c_j) + D_j(N mod 31)
with a_j | 2^m 3, b_j | 2.3.5, c_j | 4.7.  The tables are written to TK_compact.txt, and
the resulting function is checked against TK_series.txt.
"""
import sys
import json
from fractions import Fraction as Fr
from math import lcm

K = int(sys.argv[1])
comp = json.load(open(f'components_{K}.json'))
coef = {}
for j, cs in comp.items():
    groups = {}
    for d, g in cs.items():
        d = int(d)
        key = next((p for p in (5, 7, 31) if d % p == 0), 1)
        groups.setdefault(key, []).append((d, [Fr(x) for x in g]))
    tabs = {}
    for key, lst in sorted(groups.items()):
        m = lcm(*[d for d, _ in lst])
        tabs[key] = (m, [sum(g[r % d] for d, g in lst) for r in range(m)])
    coef[int(j)] = tabs


def T(N):
    return sum(sum(t[N % m] for m, t in coef[j].values()) * N**j for j in coef)


ser = {int(l.split()[0]): int(l.split()[1]) for l in open(f'T{K}_series.txt')}
for n, v in ser.items():
    assert T(n) == v, n
print(f'compact form = exact series for N = 1..{max(ser)}')
with open(f'T{K}_compact.txt', 'w') as f:
    f.write(f'# T(N,{K}) = sum_j N^j * sum_tables table[N mod m]\n'
            f'# line: j  group  m  values for N mod m = 0..m-1\n')
    for j in sorted(coef, reverse=True):
        for key, (m, t) in coef[j].items():
            f.write(f'{j} {key} {m} ' + ' '.join(str(x) for x in t) + '\n')
            print(f'c_{j}: group {key}: N mod {m}' + (': ' + ' '.join(map(str, t)) if m <= 48 else ''))
