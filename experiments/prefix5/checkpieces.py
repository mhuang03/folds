"""checkpieces.py K PIECESFILE: class-by-class check.  For every (N, key, count) line produced by
../prefix/pieces.c (direct enumeration, one line per nonempty (order type, sign matrix) class),
the coefficient of t^N in that class's Normaliz generating function must equal count, and
every class with a nonzero coefficient must appear."""
import sys
import json

K, fn = int(sys.argv[1]), sys.argv[2]
L = [json.loads(l) for l in open(f'classes_{K}.json')]
nsig = 3 ** (K * (K - 1) // 2)


def key(c):
    pi = c['pi']
    code = 0
    for i in range(K):
        code = code * (K - i) + sum(1 for j in range(i + 1, K) if pi[j] < pi[i])
    sig = {(i, j): v for i, j, v in c['sig']}
    sc = 0
    for j in range(1, K):
        for i in range(j):
            sc = sc * 3 + sig[(i, j)] + 1
    return code * nsig + sc


def coeff(c, n):
    a = [0] * (n + 1)
    for i, v in enumerate(c['num']):
        if c['shift'] + i <= n:
            a[c['shift'] + i] += v
    for d in c['den']:
        for i in range(d, n + 1):
            a[i] += a[i - d]
    return a[n]


data = {}
for l in open(fn):
    n, k, v = map(int, l.split())
    data.setdefault(n, {})[k] = v
for n, d in sorted(data.items()):
    mine = {key(c): coeff(c, n) for c in L}
    mine = {k: v for k, v in mine.items() if v}
    assert mine == d, n
    print(f'N={n}: all {len(d)} class counts agree with pieces.c')
