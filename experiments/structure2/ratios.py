"""Item 2: r(N) = a(N)/a(N-1), r(N)/N, y(N) = ln a(N) - ln a_W(N), and the mod-6 pattern.
Model selection for periodic corrections on the exact data N <= 38; comparison with the
SMC deficit fit (experiments/asymptotics/NOTES.txt section 3.4, form D)."""
import math
import numpy as np
from common import counts

a, s = counts()
NN = sorted(a)


def lnW(N):
    """ln of the Wallis/independence model a_W(N) = N! prod_m 4^r r!^2/(2r+1)!."""
    t = math.lgamma(N + 1)
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        t += r * math.log(4) + 2 * math.lgamma(r + 1) - math.lgamma(2 * r + 2)
    return t


la = {N: math.log(a[N]) for N in NN}
y = {N: la[N] - lnW(N) for N in NN}
d = {N: (math.lgamma(N + 1) - la[N]) / N for N in NN}

print(' N   r(N)      r/N     y(N)     y/N     d(N)    rD/N(model D)')
for N in NN[1:]:
    r = a[N] / a[N - 1]
    LL = math.log(N)
    # form D: N d(N) = N(1.69 lnln N - 1.675 + 1.83/ln N); r/N = exp(-(N d)')
    der = 1.69 * math.log(LL) - 1.675 + 1.83 / LL + 1.69 / LL - 1.83 / LL**2
    print(f'{N:2d} {r:9.4f} {r/N:8.5f} {y[N]:8.4f} {y[N]/N:8.5f} {d[N]:8.4f} {math.exp(-der):8.5f}'
          f'  {"*" if N % 3 == 0 else ""}')

# ---- model selection on y(N), N0..38 -------------------------------------------------
N0 = 10
X = [N for N in NN if N >= N0]
Y = np.array([y[N] for N in X])


def design(kind):
    cols, names = [], []
    for f, nm in ((lambda N: 1.0, '1'), (lambda N: N, 'N'), (lambda N: math.log(N), 'lnN'),
                  (lambda N: N / math.log(N), 'N/lnN')):
        cols.append([f(N) for N in X]); names.append(nm)
    if 'par' in kind:      # parity offset
        cols.append([N % 2 for N in X]); names.append('odd')
    if 'par/N' in kind:
        cols.append([(N % 2) / N for N in X]); names.append('odd/N')
    if 'm3' in kind:       # 3 | N indicator
        cols.append([float(N % 3 == 0) for N in X]); names.append('[3|N]')
    if 'm3/N' in kind:
        cols.append([float(N % 3 == 0) / N for N in X]); names.append('[3|N]/N')
    if 'm6' in kind:       # full mod-6 constants
        for r in range(1, 6):
            cols.append([float(N % 6 == r) for N in X]); names.append(f'[N=={r} mod 6]')
    if 'm6/N' in kind:
        for r in range(1, 6):
            cols.append([float(N % 6 == r) / N for N in X]); names.append(f'[{r}]/N')
    if 'm4' in kind:
        cols.append([float(N % 4 == 0) for N in X]); names.append('[4|N]')
    if 'm5' in kind:
        cols.append([float(N % 5 == 0) for N in X]); names.append('[5|N]')
    return np.array(cols).T, names


print(f'\nModel selection for y(N), N = {N0}..38 ({len(X)} points); smooth part 1, N, lnN, N/lnN')
res = {}
for kind in ([], ['par'], ['par', 'm3'], ['par', 'm3/N'], ['par', 'par/N', 'm3', 'm3/N'],
             ['m6'], ['m6/N'], ['par', 'm3', 'm4'], ['par', 'm3', 'm5'], ['m6', 'm6/N']):
    A_, names = design(kind)
    coef, *_ = np.linalg.lstsq(A_, Y, rcond=None)
    rr = Y - A_ @ coef
    n, k = len(Y), A_.shape[1]
    rss = float(rr @ rr)
    aic = n * math.log(rss / n) + 2 * k
    sd = math.sqrt(rss / max(n - k, 1))
    cov = np.linalg.pinv(A_.T @ A_) * sd**2
    se = np.sqrt(np.diag(cov))
    tag = '+'.join(kind) or 'none'
    print(f' {tag:24s} k={k:2d} resid sd={sd:.4f} AIC={aic:7.1f}   ' +
          ', '.join(f'{nm}={c:+.4f}({e:.4f})' for nm, c, e in zip(names, coef, se) if nm not in ('1', 'N', 'lnN', 'N/lnN')))
    res[tag] = rr

print('\nresiduals of model par+m3 by N (x1000):')
print(' '.join(f'{N}:{1000*v:+.0f}' for N, v in zip(X, res['par+m3'])))

# ---- the bump sequence b(N) = y(N) - (y(N-2)+y(N+2))/2 and N*b(N) --------------------
print('\nlocal bump b(N) = y(N) - (y(N-2)+y(N+2))/2 ; N*b ; N^2*b')
for N in NN:
    if N - 2 in y and N + 2 in y and N >= 6:
        b = y[N] - (y[N - 2] + y[N + 2]) / 2
        print(f'{N:2d}{"*" if N % 3 == 0 else " "} b={b:+.4f} N*b={N*b:+.3f} N^2 b={N*N*b:+.2f}')

# ---- curvature-free version: 6-step second difference within residue classes ---------
print('\nsixth-step bump B6(N) = y(N) - (y(N-1)+y(N+1))/2 averaged per class mod 6 over N >= 20')
from collections import defaultdict
acc = defaultdict(list)
for N in NN:
    if N - 1 in y and N + 1 in y and N >= 20:
        acc[N % 6].append(N * (y[N] - (y[N - 1] + y[N + 1]) / 2))
for r in range(6):
    print(f' N=={r} mod 6: N*bump = ' + ' '.join(f'{v:+.3f}' for v in acc[r]))

# ---- ratios r(N)/N periodic pattern -------------------------------------------------
print('\nlog r(N) - smooth: fit ln(r/N) on N=12..38 by (1, 1/lnN, lnlnN) + [3|N] + parity')
X2 = [N for N in NN if N >= 12]
Z = np.array([math.log(a[N] / a[N - 1] / N) for N in X2])
A2 = np.array([[1, 1 / math.log(N), math.log(math.log(N)), N % 2, float(N % 3 == 0),
                float(N % 3 == 1)] for N in X2])
c2, *_ = np.linalg.lstsq(A2, Z, rcond=None)
r2 = Z - A2 @ c2
print(' coef [1, 1/lnN, lnlnN, odd, [N==0 mod3], [N==1 mod 3]] =', np.round(c2, 4),
      ' resid sd', round(float(np.std(r2)), 4))
print(' resid:', ' '.join(f'{N}:{v:+.3f}' for N, v in zip(X2, r2)))

# ---- r(N)/N far out: interval geometric means from the SMC estimates ------------------
smc = {48: 89.0, 64: 130.5, 96: 222.0, 128: 321.6, 192: 538.6, 256: 772.4, 384: 1275.8,
       512: 1816.1, 768: 2964.6, 1024: 4182.0, 1536: 6762.6, 2048: 9494.4, 4096: 21269.0}
smc[38] = la[38]; smc[32] = la[32]
print('\ninterval geometric mean of r(N)/N from SMC ln a (NOTES 3.2); x = r/N')
ks = sorted(smc)
for N1, N2 in zip(ks, ks[1:]):
    g = (smc[N2] - smc[N1] - (math.lgamma(N2 + 1) - math.lgamma(N1 + 1))) / (N2 - N1)
    x = math.exp(g); Nm = math.sqrt(N1 * N2); L = math.log(Nm)
    print(f' {N1:5d}-{N2:5d}: r/N={x:.4f}  x*lnN={x*L:.3f}  x*lnN^1.5={x*L**1.5:.3f}'
          f'  x*lnN^1.69={x*L**1.69:.3f}')
