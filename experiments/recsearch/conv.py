"""Family 3a: convolution, cubic and divisor-sum recurrences.

Ansatz:  sum_{b in TB} c_b b(N) a(N) = sum_{t in TERMS} sum_{b in B} c_{t,b} b(N) t(N),
TERMS chosen from the list below (all exact functions of a(1..N-1) and N).
Unknowns are linear, all available N are used; genuine = target coefficient non-zero.
"""
from itertools import combinations
from math import comb, factorial
from fractions import Fraction
from common import A, NMAX, analyze, fmt


def a0(k):          # a with a(0) = 1
    return 1 if k == 0 else A[k]


def divs(n):
    return [d for d in range(1, n + 1) if n % d == 0]


TERMS = {
    'p1': lambda N: A[N - 1],
    'p2': lambda N: A[N - 2] if N >= 3 else None,
    'conv': lambda N: sum(A[k] * A[N - k] for k in range(1, N)),
    'conv k(N-k)': lambda N: sum(k * (N - k) * A[k] * A[N - k] for k in range(1, N)),
    'conv C(N,k)': lambda N: sum(comb(N, k) * A[k] * A[N - k] for k in range(1, N)),
    'conv C(N-2,k-1)': lambda N: sum(comb(N - 2, k - 1) * A[k] * A[N - k] for k in range(1, N)),
    'conv k even': lambda N: sum(A[k] * A[N - k] for k in range(2, N, 2)),
    'conv |N-2k|': lambda N: sum(abs(N - 2 * k) * A[k] * A[N - k] for k in range(1, N)),
    'conv 2^min': lambda N: sum(2 ** min(k, N - k) * A[k] * A[N - k] for k in range(1, N)),
    'cubic': lambda N: sum(A[i] * A[j] * A[N - i - j] for i in range(1, N) for j in range(1, N - i)),
    'cubic multinom': lambda N: sum(factorial(N) // (factorial(i) * factorial(j) * factorial(N - i - j))
                                    * A[i] * A[j] * A[N - i - j] for i in range(1, N) for j in range(1, N - i)),
    'div a(d)': lambda N: sum(A[d] for d in divs(N) if d < N),
    'div a(d)a(N/d)^d': lambda N: sum(A[d] * A[N // d] ** d for d in divs(N) if 1 < d < N),
    'div a(N/d)^d': lambda N: sum(A[N // d] ** d for d in divs(N) if 1 < d),
    'splits 2a(jn)a((j+1)n)': lambda N: sum(2 * A[(q // 2) * (N // q)] * A[(q // 2 + 1) * (N // q)]
                                           for q in divs(N) if q % 2 == 1 and q > 1),
}

BASES = {
    '1': [lambda N: 1],
    '1,N': [lambda N: 1, lambda N: N],
    '1,N,N^2': [lambda N: 1, lambda N: N, lambda N: N * N],
    'N^0..3': [lambda N, j=j: N ** j for j in range(4)],
    'par: 1,(-1)^N': [lambda N: 1, lambda N: (-1) ** N],
    'par: 1,N,(-1)^N,N(-1)^N': [lambda N: 1, lambda N: N, lambda N: (-1) ** N, lambda N: N * (-1) ** N],
    '1,2^N': [lambda N: 1, lambda N: 2 ** N],
}


def run(terms, B, TB, Ns):
    rows = []
    for N in Ns:
        vals = [TERMS[t](N) for t in terms]
        if any(v is None for v in vals):
            continue
        rows.append([b(N) * v for v in vals for b in B] + [-b(N) * A[N] for b in TB])
    K = len(rows[0])
    return analyze(rows, list(range(K - len(TB), K)))


def main():
    Ns = list(range(3, NMAX + 1))
    names = list(TERMS)
    singles = [[t] for t in names]
    combos = []
    # every single term, every term together with a(N-1), with a(N-1),a(N-2);
    # every pair of convolution-type terms; the full convolution family at once.
    for t in names:
        combos.append([t])
        if t not in ('p1', 'p2'):
            combos.append(['p1', t])
            combos.append(['p1', 'p2', t])
    conv_like = [t for t in names if t.startswith('conv') or t.startswith('cubic')]
    for t, u in combinations(conv_like, 2):
        combos.append(['p1', t, u])
    combos.append(['p1', 'p2'] + conv_like)
    combos.append(['p1', 'p2'] + [t for t in names if t.startswith('div') or t.startswith('splits')])
    combos.append(names)
    n_run = 0
    best = []
    gens = []
    for terms in combos:
        for bname, B in BASES.items():
            for tbname, TB in (('1', BASES['1']), ('same', B)):
                if tbname == 'same' and bname == '1':
                    continue
                if (len(terms) * len(B) + len(TB)) + 5 > len(Ns):
                    continue
                res = run(terms, B, TB, Ns)
                n_run += 1
                line = f"{'+'.join(terms)[:70]:70s} B={bname:24s} TB={tbname:4s} " + fmt(res)
                print(line, flush=True)
                if res.get('genuine'):
                    print('   GENUINE', res['genuine'][:1])
                    gens.append(line)
                best.append((res['excess'], line))
    best.sort(reverse=True)
    print('\nlargest excesses:')
    for b in best[:8]:
        print(' ', b[1])
    print(f'\n{n_run} ansatze run; {len(gens)} with a genuine relation')


if __name__ == '__main__':
    main()
