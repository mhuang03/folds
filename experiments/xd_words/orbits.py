"""Item 2: the functional graph phi(b) = 2b+1 on Z/N (boundary m-1 -> boundary 2m-1), i.e. the
doubling map m -> 2m on Z/N in panel coordinates (panel N = residue 0 is the fixed point).

For each N: the 2-part 2^a, the odd part q, the number of cycles, the multiset of cycle
lengths, ord_q(2), tree depth a.  Then a(N) against this structure: the residual of
y(N) = ln a(N) - ln a_W(N) after the smooth part and the known parity and [3|N]/N terms
(model 'par+m3/N' of experiments/structure2), regressed on orbit statistics."""
import math, os, sys
from collections import Counter
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def counts():
    a = {}
    for line in open(os.path.join(HERE, '..', 'semi_counts.txt')):
        if line.startswith('#') or not line.strip():
            continue
        p = line.split()
        a[int(p[0])] = int(p[1])
    return a


def orbit_stats(N):
    """Cycle structure of m -> 2m mod N on Z/N."""
    a, q = 0, N
    while q % 2 == 0:
        q //= 2
        a += 1
    seen = [False] * N
    lens = Counter()
    # the periodic points are the multiples of 2^a
    step = N // q
    for m in range(0, N, step):
        if seen[m]:
            continue
        L, x = 0, m
        while not seen[x]:
            seen[x] = True
            x = 2 * x % N
            L += 1
        lens[L] += 1
    order = 1
    if q > 1:
        x = 2 % q
        while x != 1:
            x = 2 * x % q
            order += 1
    return dict(a=a, q=q, ncyc=sum(lens.values()), lens=dict(sorted(lens.items())), ord=order,
                nper=q)


def lnW(N):
    t = math.lgamma(N + 1)
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        t += r * math.log(4) + 2 * math.lgamma(r + 1) - math.lgamma(2 * r + 2)
    return t


def main():
    a = counts()
    NN = sorted(a)
    y = {N: math.log(a[N]) - lnW(N) for N in NN}
    X = [N for N in NN if N >= 10]
    Y = np.array([y[N] for N in X])
    base = [[1.0, N, math.log(N), N / math.log(N), N % 2, float(N % 3 == 0) / N] for N in X]
    B = np.array(base)
    coef, *_ = np.linalg.lstsq(B, Y, rcond=None)
    res = Y - B @ coef
    sd0 = math.sqrt(float(res @ res) / (len(Y) - B.shape[1]))
    st = {N: orbit_stats(N) for N in X}
    print('Functional graph of the doubling map on Z/N, and the residual of ln a(N)')
    print('(residual = y(N) - smooth(1,N,lnN,N/lnN) - parity - [3|N]/N ; sd = %.4f, %d points)' % (sd0, len(X)))
    print('  N  2^a  odd q  ord_q(2)  #cycles  cycle lengths (len:count)            resid*1000')
    for N, r in zip(X, res):
        s = st[N]
        print(f' {N:2d}  {2**s["a"]:3d}  {s["q"]:5d}  {s["ord"]:8d}  {s["ncyc"]:7d}  {str(s["lens"]):36s} {1000*r:+7.1f}')

    def test(name, f):
        col = np.array([f(N) for N in X], dtype=float)
        if np.allclose(col, col[0]):
            return
        A = np.column_stack([B, col])
        c, *_ = np.linalg.lstsq(A, Y, rcond=None)
        rr = Y - A @ c
        n, k = A.shape
        sd = math.sqrt(float(rr @ rr) / (n - k))
        cov = np.linalg.pinv(A.T @ A) * sd ** 2
        se = math.sqrt(cov[-1, -1])
        corr = np.corrcoef(res, col - col.mean())[0, 1]
        print(f'  {name:34s} coef {c[-1]:+.5f} +- {se:.5f}  t = {c[-1]/se:+5.2f}   corr with resid {corr:+.2f}   sd {sd:.4f}')

    print('\nOne extra regressor at a time (|t| > 2.8 would be significant at the 1% level, 23 d.o.f.;')
    print('with ~20 regressors tried, expect one |t| > 2 by chance):')
    test('#cycles', lambda N: st[N]['ncyc'])
    test('#cycles / N', lambda N: st[N]['ncyc'] / N)
    test('ln #cycles', lambda N: math.log(st[N]['ncyc']))
    test('ord_q(2)', lambda N: st[N]['ord'])
    test('ord_q(2) / N', lambda N: st[N]['ord'] / N)
    test('tree depth a = v2(N)', lambda N: st[N]['a'])
    test('[N power of 2]', lambda N: float(st[N]['q'] == 1))
    test('[N = 2^L - 1]', lambda N: float((N + 1) & N == 0))
    test('[N = 2^L + 1]', lambda N: float((N - 1) & (N - 2) == 0))
    test('[N prime]', lambda N: float(all(N % p for p in range(2, N))))
    test('[2 primitive root mod odd part q>1]', lambda N: float(st[N]['q'] > 1 and st[N]['ord'] == st[N]['q'] - 1))
    test('[4 | N]', lambda N: float(N % 4 == 0))
    test('[5 | N]  (4-cycle N/5..)', lambda N: float(N % 5 == 0))
    test('[5 | N] / N', lambda N: float(N % 5 == 0) / N)
    test('[7 | N]  (two 3-cycles)', lambda N: float(N % 7 == 0))
    test('[7 | N] / N', lambda N: float(N % 7 == 0) / N)
    test('[9 | N]  (6-cycle)', lambda N: float(N % 9 == 0))
    test('[15 | N]', lambda N: float(N % 15 == 0))
    test('#cycles of length <= 4', lambda N: sum(c for L, c in st[N]['lens'].items() if L <= 4))
    test('#periodic points of period <= 4 /N', lambda N: sum(L * c for L, c in st[N]['lens'].items() if L <= 4) / N)
    test('[3 | N] (constant, on top of /N)', lambda N: float(N % 3 == 0))
    test('[N = 1 mod 3]', lambda N: float(N % 3 == 1))

    print('\nRaw ratios for special N (r(N)/N = a(N)/(N a(N-1))):')
    for N in NN:
        if N >= 5:
            tag = []
            if N & (N - 1) == 0: tag.append('2^L')
            if (N + 1) & N == 0: tag.append('2^L-1')
            if (N - 1) & (N - 2) == 0: tag.append('2^L+1')
            if tag:
                print(f'  N={N:2d} {",".join(tag):10s} r/N = {a[N]/a[N-1]/N:.4f}   neighbours same parity: '
                      + ', '.join(f'{M}:{a[M]/a[M-1]/M:.4f}' for M in (N - 2, N + 2) if M in a and M - 1 in a))


if __name__ == '__main__':
    main()
