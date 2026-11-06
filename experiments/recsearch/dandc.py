"""Family 2: divide-and-conquer and mixed recurrences.

Ansatz (linear in the unknowns c):
    sum_{b in TB} c_b b(N) a(N)  =  sum_{t in TERMS} sum_{b in B} c_{t,b} b(N) t(N)
over a set of N (all N, even N or odd N).  TERMS are monomials in "neighbour" values
such as a(n), a(n-1), a(n+1) (n = floor(N/2)), a(N-1), a(N-2), and B, TB are
coefficient bases (polynomials in N, 2^n, 4^n, 2^N, ...).  A solution is genuine only
if some target coefficient c_b is non-zero.  Every ansatz uses ALL available N (the
first equations are the 'fit', the last E-K are held out automatically: a nonzero
solution of the whole system is needed); nfit/excess report near-misses.
"""
from itertools import combinations_with_replacement as cwr
from fractions import Fraction
from common import A, NMAX, analyze, fmt


def av(k):
    return A[k] if 1 <= k <= NMAX else None


# neighbour values (None if undefined)
V = {
    'h': lambda N: av(N // 2),              # a(floor N/2)
    'H': lambda N: av((N + 1) // 2),        # a(ceil N/2)
    'h-': lambda N: av(N // 2 - 1),         # a(floor N/2 - 1)
    'H+': lambda N: av((N + 1) // 2 + 1),   # a(ceil N/2 + 1)
    'p1': lambda N: av(N - 1),              # a(N-1)
    'p2': lambda N: av(N - 2),              # a(N-2)
    'q': lambda N: av(N // 4),              # a(floor N/4)
}

BASES = {
    '1': [lambda N: 1],
    '1,N': [lambda N: 1, lambda N: N],
    '1,N,N^2': [lambda N: 1, lambda N: N, lambda N: N * N],
    'N^0..3': [lambda N, j=j: N ** j for j in range(4)],
    'N^0..5': [lambda N, j=j: N ** j for j in range(6)],
    '1,2^n': [lambda N: 1, lambda N: 2 ** (N // 2)],
    '1,4^n': [lambda N: 1, lambda N: 4 ** (N // 2)],
    '1,N,2^n,N2^n': [lambda N: 1, lambda N: N, lambda N: 2 ** (N // 2), lambda N: N * 2 ** (N // 2)],
    '1,2^n,4^n': [lambda N: 1, lambda N: 2 ** (N // 2), lambda N: 4 ** (N // 2)],
    '1,2^N': [lambda N: 1, lambda N: 2 ** N],
}


def monomials(vars_, degs):
    out = []
    for d in degs:
        for m in cwr(vars_, d):
            out.append(m)
    return out


def mono_val(m, N):
    v = 1
    for x in m:
        y = V[x](N)
        if y is None:
            return None
        v *= y
    return v


def run_ansatz(Ns, monos, B, TB):
    rows = []
    for N in Ns:
        vals = [mono_val(m, N) if m else 1 for m in monos]
        if any(v is None for v in vals):
            continue
        row = [b(N) * v for v in vals for b in B] + [-b(N) * A[N] for b in TB]
        rows.append(row)
    if not rows:
        return None
    K = len(rows[0])
    tcols = list(range(K - len(TB), K))
    return analyze(rows, tcols)


PARITY = {
    'even': [N for N in range(1, NMAX + 1) if N % 2 == 0],
    'odd': [N for N in range(1, NMAX + 1) if N % 2 == 1],
    'all': list(range(1, NMAX + 1)),
}

# (label, parity, variables, degree set)
SHAPES = [
    ('a(2n)=P(a(n-1),a(n),a(n+1)) deg<=2', 'even', ['h-', 'h', 'H+'], [0, 1, 2]),
    ('a(2n)=P(a(n),a(n+1)) deg<=2', 'even', ['h', 'H+'], [0, 1, 2]),
    ('a(2n)=P(a(n),a(n+1)) deg 2 hom', 'even', ['h', 'H+'], [2]),
    ('a(2n)=P(a(n-1),a(n),a(n+1)) deg 2 hom', 'even', ['h-', 'h', 'H+'], [2]),
    ('a(2n)=P(a(n)) deg<=4', 'even', ['h'], [0, 1, 2, 3, 4]),
    ('a(2n)=c a(n)^2', 'even', ['h'], [2]),
    ('a(2n+1)=Q(a(n),a(n+1)) deg<=2', 'odd', ['h', 'H'], [0, 1, 2]),
    ('a(2n+1)=Q(a(n),a(n+1)) deg 2 hom', 'odd', ['h', 'H'], [2]),
    ('a(2n+1)=Q(a(n-1),a(n),a(n+1),a(n+2)) deg 2 hom', 'odd', ['h-', 'h', 'H', 'H+'], [2]),
    ('a(2n+1)=c a(n)a(n+1)', 'odd', ['hH'], None),
    ('a(N)=al a(N-1)+be a(n)^2', 'all', None, [('p1',), ('h', 'h')]),
    ('a(N)=al a(N-1)+be a(n)a(N-n)', 'all', None, [('p1',), ('h', 'H')]),
    ('a(N)=al a(N-1)+be a(n)^2+ga a(n)a(N-n)', 'all', None, [('p1',), ('h', 'h'), ('h', 'H')]),
    ('a(N)=al a(N-1)+be a(N-2)+ga a(n)a(N-n)', 'all', None, [('p1',), ('p2',), ('h', 'H')]),
    ('a(N)=al a(N-1)+be a(N-2)+ga a(n)a(N-n)+de a(n)^2', 'all', None, [('p1',), ('p2',), ('h', 'H'), ('h', 'h')]),
    ('a(N)=al a(N-1)+be a(n)a(N-n) [even]', 'even', None, [('p1',), ('h', 'H')]),
    ('a(N)=al a(N-1)+be a(n)a(N-n) [odd]', 'odd', None, [('p1',), ('h', 'H')]),
    ('a(N)=al a(N-1)+be a(N-2)+ga a(n)a(N-n) [even]', 'even', None, [('p1',), ('p2',), ('h', 'H')]),
    ('a(N)=al a(N-1)+be a(N-2)+ga a(n)a(N-n) [odd]', 'odd', None, [('p1',), ('p2',), ('h', 'H')]),
    ('a(N)=al a(N-1)+be a(n)^2 a(N-n)^2/a(N-1) style: a(N)a(N-1)=al a(N-1)^2+be (a(n)a(N-n))^2', 'all', None,
     [('p1', 'p1'), ('h', 'H', 'h', 'H'), ('p1', 'p2')]),
    ('a(4m)=P(a(m)) deg 4 hom + a(2m)^2', 'all4', None, [('q', 'q', 'q', 'q'), ('h', 'h')]),
    ('a(N)=al a(N-1)+be a(N-2)+ga a(n)a(N-n)+de a(q)^4', 'all', None, [('p1',), ('p2',), ('h', 'H'), ('q', 'q', 'q', 'q')]),
]


def main():
    out = []
    best = []
    PARITY['all4'] = [N for N in range(4, NMAX + 1, 4)]
    for label, par, vars_, degs in SHAPES:
        if vars_ is None:
            monos = [tuple(m) for m in degs]
        elif vars_ == ['hH']:
            monos = [('h', 'H')]
        else:
            monos = [m for m in monomials(vars_, degs)]
        for bname, B in BASES.items():
            for tbname, TB in (('1', BASES['1']), ('same', B)):
                if tbname == 'same' and bname == '1':
                    continue
                res = run_ansatz(PARITY[par], monos, B, TB)
                if res is None:
                    continue
                if res['E'] - res['K'] < 3:
                    continue
                gen = res.get('genuine', [])
                line = f"{label:62s} B={bname:13s} TB={tbname:4s} " + fmt(res)
                out.append(line)
                print(line, flush=True)
                if gen:
                    print('   GENUINE', gen[:1])
                best.append((res['excess'], line))
    best.sort(reverse=True)
    print('\nlargest excesses:')
    for b in best[:8]:
        print(' ', b[1])
    print(f'\n{len(out)} ansatze run; genuine relations: see GENUINE lines (none if absent)')


if __name__ == '__main__':
    main()
