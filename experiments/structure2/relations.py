"""Item 4: exact linear relations with polynomial coefficients among shifted refined sequences.
For a target X and a pool of sequences Y, we look for c with
    sum_{Y in pool, 0<=j<=J, 0<=p<=P} c_{Y,j,p} N^p Y(N-j) = 0     for all N in a range,
by computing the exact rational nullspace of the matrix (rows = N, cols = basis terms).
A relation is reported only if #rows >= #cols + 4 (overdetermined by at least 4)."""
import os, itertools
import sympy
from common import counts, selfdual, stats, ROOT

a, s = counts()
c = selfdual()
J = {}; I = {}
for line in open(os.path.join(ROOT, 'experiments', 'jseq', 'out', 'data.txt')):
    p = line.split()
    if p and p[0] == 'N':
        J[int(p[1])] = int(p[5]); I[int(p[1])] = int(p[7])
D = {n: stats(n) for n in range(2, 31)}
Ds = {n: stats(n, 'sym') for n in range(2, 29)}
seq = {
    'a': a, 'c': c, 'J': J, 'I': I,
    'F1': {n: D[n]['F'][0] for n in D}, 'F2': {n: D[n]['F'][1] for n in D},
    'F3': {n: D[n]['F'][2] for n in D if n >= 3},
    'Fmid': {n: D[n]['F'][(n + 1) // 2 - 1] for n in D},
    'TN2': {n: D[n]['prefixes'][n - 2] for n in D},
    'TN3': {n: D[n]['prefixes'][n - 3] for n in D if n >= 3},
    'R': {n: sum(D[n]['reach']) for n in D},
    'P1N': {n: D[n]['F2'][0][n - 1] for n in D},      # starts (1, N)
    's': {n: Ds[n]['total'] for n in Ds},
    'sF1': {n: Ds[n]['F'][0] for n in Ds},
}
seq['EO'] = {n: sum(D[n]['F'][1::2]) - sum(D[n]['F'][0::2]) for n in D}


def search(target, pool, Jmax, P, Nmin=6, extra=()):
    cols, names = [], []
    for nm in [target] + list(pool):
        for j in range(0 if nm == target else 0, Jmax + 1):
            if nm == target and j == 0:
                pass
            for p in range(P + 1):
                names.append((nm, j, p))
    for nm, f in extra:
        names.append((nm, 0, 0))
    Ns = [N for N in range(Nmin, 60)
          if all((N - j) in seq[nm] for nm, j, p in names if nm in seq)]
    if len(Ns) < len(names) + 4:
        return None, len(Ns), len(names)
    ex = dict(extra)
    M = sympy.Matrix([[(N ** p) * seq[nm][N - j] if nm in seq else ex[nm](N)
                       for nm, j, p in names] for N in Ns])
    ns = M.nullspace()
    # keep only relations that involve the target at shift 0
    good = [v for v in ns if any(v[i] != 0 for i, t in enumerate(names) if t[0] == target and t[1] == 0)]
    return (good, names), len(Ns), len(names)


def conv(N, f=a):
    return sum(f[i] * f[N - i] for i in range(1, N) if i in f and (N - i) in f)


if __name__ == '__main__':
    tests = []
    for tgt in ['a', 'c', 'F1', 'F2', 'Fmid', 'TN2', 'TN3', 'EO', 'J', 'P1N', 'R', 's', 'sF1']:
        others = [x for x in ['a', 'c', 'F1', 'Fmid', 'TN2', 'J'] if x != tgt]
        for pool in itertools.chain(*[itertools.combinations(others, k) for k in (0, 1, 2)]):
            for Jm, P in ((1, 0), (2, 0), (1, 1), (3, 0), (2, 1), (1, 2), (4, 0), (3, 1)):
                tests.append((tgt, pool, Jm, P))
    nfound = 0; ntested = 0
    for tgt, pool, Jm, P in tests:
        r, nrows, ncols = search(tgt, pool, Jm, P)
        if r is None:
            continue
        ntested += 1
        good, names = r
        if good:
            nfound += 1
            for v in good:
                print('RELATION', tgt, pool, Jm, P,
                      [(names[i], v[i]) for i in range(len(names)) if v[i] != 0])
    print(f'tested {ntested} (target, pool, shifts, degree) combinations with >= 4 spare rows; '
          f'relations found: {nfound}')

    # convolution-type bases for a and c
    print('\nconvolution bases:')
    for tgt in ['a', 'c', 'J', 'F1', 'TN2']:
        extra = [('conv_a', lambda N: conv(N)), ('a(n)a(n+1)', lambda N: a[N // 2] * a[(N + 1) // 2]),
                 ('2^N', lambda N: 2 ** N), ('N!', lambda N: sympy.factorial(N))]
        r, nrows, ncols = search(tgt, ['a'] if tgt != 'a' else [], 2, 1, Nmin=6, extra=extra)
        print(tgt, 'rows', nrows, 'cols', ncols, 'relations' if r and r[0] else 'none')

    # c(2n) against products of a(n)
    print('\nc(2n) vs a(n): ratios')
    for n in range(2, 21):
        if 2 * n in c and n + 1 in a:
            print(n, c[2 * n], f'c(2n)/a(n)^2={c[2*n]/a[n]**2:.4f}  c(2n)/(a(n)a(n+1))={c[2*n]/(a[n]*a[n+1]):.4f}'
                  f'  c(2n)^2/a(2n)={c[2*n]**2/a[2*n]:.4f}' if 2 * n in a else '')
    # (a polynomial-coefficient search for c(2n), c(4n+1) in products of a(n) would be
    # underdetermined with only 8 usable n; c(2n) ~ sqrt(a(2n)) anyway, see FINDINGS.)
