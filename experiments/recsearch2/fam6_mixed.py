"""Family 6: relations mixing a(N) with the side sequences c(N) (N<=41), J(N) (N<=33),
I(N) (N<=38, from identity (A)) and the prefix counts T(N,k) (N<=24).

Ansatz: sum_f p_f(N) f(N) = 0 over a feature set f (each p_f a polynomial of degree d in
N), the target column being every feature that involves a(N) itself.  Rows = all N where
every feature is known (also split into even N and odd N, per the literature notes).
Linear feature sets and homogeneous-quadratic ones; spare >= 5 always.
Note that I(N) together with the products a(fl N/2)a(cl N/2), a(N/3)a(2N/3), ... is a
trivial identity, so I is only combined with shifts of a and I, never with those products."""
import itertools
from fractions import Fraction
from common2 import A, C, J, I, T, NMAX, analyze

g = {
    'a0': lambda N: A[N], 'a1': lambda N: A[N - 1], 'a2': lambda N: A[N - 2],
    'c0': lambda N: C[N], 'c1': lambda N: C[N - 1], 'c2': lambda N: C[N - 2], 'cp1': lambda N: C[N + 1],
    'J0': lambda N: J[N], 'J1': lambda N: J[N - 1], 'J2': lambda N: J[N - 2],
    'I0': lambda N: I[N], 'I1': lambda N: I[N - 1],
    'Tm2': lambda N: T[N][N - 2], 'Tm3': lambda N: T[N][N - 3], 'Tm4': lambda N: T[N][N - 4],
    'T1m1': lambda N: T[N - 1][N - 1], 'T1m2': lambda N: T[N - 1][N - 2], 'T1m3': lambda N: T[N - 1][N - 3],
    'Th': lambda N: T[N][N // 2], 'Th1': lambda N: T[N][N // 2 + 1],
}
SETS = [
    ('a0 a1 c0 c1', 'lin'), ('a0 a1 c0 c1 c2 cp1', 'lin'), ('a0 a1 a2 c0 c1 c2', 'lin'),
    ('a0 a1 J0 J1', 'lin'), ('a0 J0 J1 J2', 'lin'), ('a0 a1 J0 J1 c0 c1', 'lin'),
    ('a0 a1 I0 I1', 'lin'), ('a0 I0 I1', 'lin'),
    ('a0 Tm2 Tm3', 'lin'), ('a0 Tm2 Tm3 Tm4', 'lin'), ('a0 T1m1 T1m2 T1m3', 'lin'),
    ('a0 Th Th1', 'lin'), ('a0 a1 Tm2 T1m2', 'lin'),
    ('a0 a1 c0 c1', 'quad'), ('a0 a1 J0 J1', 'quad'), ('a0 c0 J0', 'quad'), ('a0 a1 c0 J0', 'quad'),
    ('a0 Tm2 T1m2', 'quad'),
]

print(f"{'features':26s} {'kind':4s} {'rows':8s} {'boxes':>5s} {'K range':>9s} best excess  hits")
for fs, kind in SETS:
    names = fs.split()
    if kind == 'lin':
        feats = [(n,) for n in names]
    else:
        feats = list(itertools.combinations_with_replacement(names, 2))
    tcols_f = [i for i, f in enumerate(feats) if 'a0' in f]
    for parity in ('all', 'even', 'odd'):
        best, nb, hits, Ks = -99, 0, 0, []
        for d in range(0, 20):
            rows = []
            for N in range(3, 45):
                if parity == 'even' and N % 2:
                    continue
                if parity == 'odd' and N % 2 == 0:
                    continue
                try:
                    vals = []
                    for f in feats:
                        v = 1
                        for x in f:
                            v *= g[x](N)
                        vals.append(v)
                except (IndexError, KeyError, TypeError):
                    continue
                rows.append([Fraction(N) ** e * v for v in vals for e in range(d + 1)])
            if not rows:
                break
            K = len(rows[0])
            if len(rows) - K < 5:
                break
            tc = [i * (d + 1) + e for i in tcols_f for e in range(d + 1)]
            res = analyze(rows, target_cols=tc)
            nb += 1
            Ks.append(K)
            best = max(best, res['excess'])
            if res.get('genuine'):
                hits += 1
                print('   HIT', fs, kind, parity, d, res['genuine'][0])
        if nb:
            print(f"{fs:26s} {kind:4s} {parity:8s} {nb:5d} {min(Ks):4d}-{max(Ks):<4d} {best:+d}          {hits}")
