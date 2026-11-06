"""Family 6: brute-force symbolic search over small expression trees.

Leaves (functions of N): a(N-1), a(N-2), a(floor N/2), a(ceil N/2), a(N-3) (a(0)=1),
n = floor(N/2), 2^n, N, 2^N, N!, 1, 2, 3.
Binary operations: + - * /.  All expressions with <= LMAX leaves are enumerated
bottom-up, values are kept mod p = 2^31-1 at N = 3..37 (35 positions) and expressions
with identical value vectors are merged (observational equivalence; the first, i.e.
smallest, representative is kept).  Then the target t(N) = a(N) is looked up as
    t = E,  t = E1 + E2,  t = E1 - E2,  t = E1 * E2,  t = E1 / E2,  t = alpha * E
(alpha a free rational constant, fitted at N = 3), so the top-level searches reach
2*LMAX leaves.  FIT = agreement on N = 3..20; TEST = agreement on N = 21..37.  Every
FIT survivor is re-evaluated exactly with Fractions; it is accepted only if it matches
every held-out term exactly.  Near misses: longest initial run N = 3..k matched by any
single expression E (or alpha*E).
"""
import sys
import numpy as np
from fractions import Fraction
from math import factorial
from common import A, NMAX

P = 2147483647
NS = list(range(3, NMAX + 1))
NFIT = 20 - 3 + 1          # columns 0..17 are N = 3..20
COLS = len(NS)
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
rng = np.random.default_rng(12345)
W1 = rng.integers(1, P, COLS, dtype=np.int64)
W2 = rng.integers(1, P, COLS, dtype=np.int64)

LEAVES = [
    ('a(N-1)', lambda N: A[N - 1]),
    ('a(N-2)', lambda N: A[N - 2]),
    ('a(fl(N/2))', lambda N: A[N // 2]),
    ('a(cl(N/2))', lambda N: A[(N + 1) // 2]),
    ('a(N-3)', lambda N: A[N - 3] if N > 3 else 1),
    ('fl(N/2)', lambda N: N // 2),
    ('2^fl(N/2)', lambda N: 2 ** (N // 2)),
    ('N', lambda N: N),
    ('2^N', lambda N: 2 ** N),
    ('N!', lambda N: factorial(N)),
    ('1', lambda N: 1),
    ('2', lambda N: 2),
    ('3', lambda N: 3),
]


def keys(M, ncol=COLS):
    k1 = np.zeros(M.shape[0], dtype=np.int64)
    k2 = np.zeros(M.shape[0], dtype=np.int64)
    for i in range(ncol):
        k1 = (k1 + M[:, i] * W1[i]) % P
        k2 = (k2 + M[:, i] * W2[i]) % P
    return k1 * P + k2


def inv(M):
    """elementwise modular inverse (entries must be non-zero)."""
    r = np.ones_like(M)
    b = M.copy()
    e = P - 2
    while e:
        if e & 1:
            r = r * b % P
        b = b * b % P
        e >>= 1
    return r


# global expression table
OPS = ['+', '-', '*', '/']
rec_op, rec_l, rec_r = [], [], []
vals_by_level = {}
ids_by_level = {}
seen = set()


def add_rows(M, op, l, r, level):
    k = keys(M)
    _, first = np.unique(k, return_index=True)
    first.sort()
    keep = [i for i in first if int(k[i]) not in seen]
    if not keep:
        return
    keep = np.array(keep)
    for i in keep:
        seen.add(int(k[i]))
    base = len(rec_op)
    rec_op.extend([op] * len(keep))
    rec_l.extend(np.asarray(l)[keep].tolist())
    rec_r.extend(np.asarray(r)[keep].tolist())
    ids = np.arange(base, base + len(keep))
    vals_by_level.setdefault(level, []).append(M[keep])
    ids_by_level.setdefault(level, []).append(ids)


def build():
    M = np.array([[f(N) % P for N in NS] for _, f in LEAVES], dtype=np.int64)
    add_rows(M, 'leaf', list(range(len(LEAVES))), [-1] * len(LEAVES), 1)
    for lev in range(2, LMAX + 1):
        for i in range(1, lev):
            j = lev - i
            X = np.concatenate(vals_by_level[i]); Xi = np.concatenate(ids_by_level[i])
            Y = np.concatenate(vals_by_level[j]); Yi = np.concatenate(ids_by_level[j])
            Ynz = np.all(Y != 0, axis=1)
            Yinv = np.zeros_like(Y)
            Yinv[Ynz] = inv(Y[Ynz])
            for op in OPS:
                if op in '+*' and i > j:
                    continue
                step = max(1, 200000 // Y.shape[0])
                for s in range(0, X.shape[0], step):
                    Xs = X[s:s + step]; Xis = Xi[s:s + step]
                    if op == '+':
                        R = (Xs[:, None, :] + Y[None, :, :]) % P
                        mask = None
                    elif op == '-':
                        R = (Xs[:, None, :] - Y[None, :, :]) % P
                        mask = None
                    elif op == '*':
                        R = (Xs[:, None, :] * Y[None, :, :]) % P
                        mask = None
                    else:
                        R = (Xs[:, None, :] * Yinv[None, :, :]) % P
                        mask = np.broadcast_to(Ynz[None, :], (Xs.shape[0], Y.shape[0])).reshape(-1)
                    L_ = np.repeat(Xis, Y.shape[0]); R_ = np.tile(Yi, Xs.shape[0])
                    R = R.reshape(-1, COLS)
                    if mask is not None:
                        R, L_, R_ = R[mask], L_[mask], R_[mask]
                    if R.shape[0]:
                        add_rows(R, op, L_, R_, lev)
        n = sum(v.shape[0] for v in vals_by_level[lev])
        print(f'level {lev}: {n} distinct expressions (total {len(rec_op)})', flush=True)


def expr(i):
    op = rec_op[i]
    if op == 'leaf':
        return LEAVES[rec_l[i]][0]
    return f'({expr(rec_l[i])} {op} {expr(rec_r[i])})'


def evaluate(i, N):
    op = rec_op[i]
    if op == 'leaf':
        return Fraction(LEAVES[rec_l[i]][1](N))
    x = evaluate(rec_l[i], N); y = evaluate(rec_r[i], N)
    if op == '+':
        return x + y
    if op == '-':
        return x - y
    if op == '*':
        return x * y
    return x / y if y != 0 else None


def exact_match(f):
    """f: N -> Fraction or None. Returns (fit ok on 3..20, number of held-out matches)."""
    vals = [f(N) for N in NS]
    fit = all(vals[k] == A[NS[k]] for k in range(NFIT))
    held = sum(1 for k in range(NFIT, COLS) if vals[k] == A[NS[k]])
    return fit, held


def main():
    print(__doc__)
    build()
    allV = np.concatenate([np.concatenate(vals_by_level[l]) for l in sorted(vals_by_level)])
    allI = np.concatenate([np.concatenate(ids_by_level[l]) for l in sorted(ids_by_level)])
    t = np.array([A[N] % P for N in NS], dtype=np.int64)
    print(f'{allV.shape[0]} distinct expressions with <= {LMAX} leaves')
    kfit = keys(allV, NFIT)
    order = np.argsort(kfit); kfit_sorted = kfit[order]

    def lookup(Q, ncol):
        kq = keys(Q, ncol)
        pos = np.searchsorted(kfit_sorted, kq)
        pos[pos >= len(kfit_sorted)] = 0
        return kfit_sorted[pos] == kq, order[pos]

    results = {}
    # t = E
    hit, idx = lookup(t[None, :], NFIT)
    results['t = E'] = [(None, int(allI[idx[0]]))] if hit[0] else []
    # t = E1 + E2  <=>  t - E1 in table;  t = E1 - E2 <=> E1 = t + E2
    for name, Q in (('t = E1 + E2', (t[None, :] - allV) % P),
                    ('t = E1 - E2', (t[None, :] + allV) % P),
                    ('t = E1 * E2', None), ('t = E1 / E2', (t[None, :] * allV) % P)):
        if name == 't = E1 * E2':
            nz = np.all(allV[:, :NFIT] != 0, axis=1)
            Q = np.zeros_like(allV)
            Q[nz] = t[None, :] * inv(allV[nz]) % P
            hit, idx = lookup(Q, NFIT)
            hit &= nz
        else:
            hit, idx = lookup(Q, NFIT)
            if name == 't = E1 / E2':
                hit &= np.all(allV != 0, axis=1)     # divisor must not vanish
        results[name] = [(int(allI[i]), int(allI[idx[i]])) for i in np.nonzero(hit)[0]]
    # t = alpha * E  (normalise at N = 3)
    nz0 = allV[:, 0] != 0
    Vn = np.zeros_like(allV)
    Vn[nz0] = allV[nz0] * inv(allV[nz0, :1]) % P
    tn = t * pow(int(t[0]), P - 2, P) % P
    eq = np.all(Vn[:, :NFIT] == tn[None, :NFIT], axis=1) & nz0
    results['t = alpha*E'] = [(None, int(allI[i])) for i in np.nonzero(eq)[0]]

    print('\nFIT (N = 3..20, mod p) survivors and exact held-out test (N = 21..37):')
    accepted = []
    for name, lst in results.items():
        print(f'  {name:14s}: {len(lst)} pass the fit mod p')
        for (i, j) in lst[:50]:
            if name == 't = E':
                f = lambda N, j=j: evaluate(j, N)
                s = expr(j)
            elif name == 't = alpha*E':
                e3 = evaluate(j, 3)
                alpha = Fraction(A[3]) / e3
                f = lambda N, j=j, al=alpha: (lambda v: None if v is None else al * v)(evaluate(j, N))
                s = f'{alpha} * {expr(j)}'
            else:
                op = name.split()[3]
                def f(N, i=i, j=j, op=op):
                    x = evaluate(i, N); y = evaluate(j, N)
                    if x is None or y is None:
                        return None
                    return {'+': lambda: x + y, '-': lambda: x - y, '*': lambda: x * y,
                            '/': lambda: x / y if y else None}[op]()
                s = f'{expr(i)} {op} {expr(j)}'
            fit, held = exact_match(f)
            print(f'      {s}:  exact fit {fit}, held-out matches {held}/{COLS - NFIT}')
            if fit and held == COLS - NFIT:
                accepted.append(s)

    # near misses: longest initial agreement N = 3..k for single expressions / alpha*E
    eqm = allV == t[None, :]
    pref = np.where(eqm.all(axis=1), COLS, np.argmin(eqm, axis=1))
    eqn = (Vn == tn[None, :]) & nz0[:, None]
    prefn = np.where(eqn.all(axis=1), COLS, np.argmin(eqn, axis=1))
    print('\nNear misses (longest initial run N = 3..k matched exactly):')
    for lab, pr, sc in (('E', pref, False), ('alpha*E', prefn, True)):
        best = np.argsort(-pr)[:5]
        for b in best:
            j = int(allI[b])
            k = int(pr[b])
            if sc:
                alpha = Fraction(A[3]) / evaluate(j, 3)
                s = f'{alpha} * {expr(j)}'
                vals = [alpha * evaluate(j, N) if evaluate(j, N) is not None else None for N in NS]
            else:
                s = expr(j)
                vals = [evaluate(j, N) for N in NS]
            ex = 0
            while ex < COLS and vals[ex] == A[NS[ex]]:
                ex += 1
            print(f'  {lab:8s} matches N=3..{2 + ex:2d} exactly  ({s})')
    print('\nACCEPTED formulas:', accepted if accepted else 'none')


if __name__ == '__main__':
    main()
