"""Fits for the asymptotics of a(N) and of the imbalance spread sigma_J(N).

Data: exact a(N) for N <= 35 (../semi_counts.txt); SMC estimates from runs/prod.txt,
runs/pscan.txt, runs/big.txt (for each N the replicates with the largest P are used; the
quoted error is the replicate spread, and the bias is estimated from the change between the
two largest P); sigma_J(t) and frac(t) from runs/d_N_P_seed.txt (largest P).

Deficit  d(N) = (ln N! - ln a(N)) / N   (so  a(N) = N! e^{-N d(N)}).
Models (N >= Nmin):
  A  d = c' ln N + b                         (a(N) = N!^{1-c'+o(1)}: exponent c = 1 - c' < 1)
  B  d = alpha ln ln N + b                   (c = 1, D ~ (ln N)^alpha)
  C  d = ln(ln N + mu) + b                    (c = 1, alpha = 1, finite-size offset mu)
  D  d = alpha ln ln N + b + e / ln N
  E  d = ln(sqrt(2 pi)) + mean_t ln sigma_J(t) - G   (the local-CLT prediction, no fit)
sigma_J(N) at t = 1/2:
  s1 sigma = a ln N + b;  s2 sigma = A (ln N - ln sigma) + B;  s3 sigma = C N^g;  s4 sigma = C (ln N)^beta
"""
import glob, math, re, sys
from collections import defaultdict
import numpy as np

Nmin = int(sys.argv[1]) if len(sys.argv) > 1 else 48

est = defaultdict(lambda: defaultdict(list))
for fn in ['runs/prod.txt', 'runs/pscan.txt', 'runs/big.txt']:
    try:
        for l in open(fn):
            m = re.match(r'N=(\d+) P=(\d+) Pmax=\d+ loga_est=([\d.]+)', l)
            if m:
                est[int(m[1])][int(m[2])].append(float(m[3]))
    except FileNotFoundError:
        pass
pts = {}
for l in open('../semi_counts.txt'):
    if l.startswith('#'):
        continue
    n, v = l.split()[:2]
    pts[int(n)] = (math.log(int(v)), 0.0, 0.0)
for N, byP in est.items():
    Ps = sorted(byP)
    top = byP[Ps[-1]]
    mu = sum(top) / len(top)
    sd = (sum((x - mu) ** 2 for x in top) / (len(top) - 1)) ** .5 if len(top) > 1 else float('nan')
    bias = 0.0
    if len(Ps) > 1:
        prev = byP[Ps[-2]]; mp = sum(prev) / len(prev)
        # bias ~ -b/P: estimate b from the two largest P, extrapolate
        b = (mu - mp) / (1 / Ps[-2] - 1 / Ps[-1]) if Ps[-1] != Ps[-2] else 0
        bias = max(0.0, b / Ps[-1])
    pts[N] = (mu, sd, bias)

print(f"{'N':>5} {'ln a(N)':>10} {'sd':>6} {'bias+':>6} {'d(N)':>8} {'e^d/lnN':>8}")
Ns = sorted(pts)
for N in Ns:
    y, sd, bias = pts[N]
    d = (math.lgamma(N + 1) - y) / N
    print(f"{N:5d} {y:10.2f} {sd:6.2f} {bias:6.2f} {d:8.4f} {math.exp(d) / math.log(N) if N > 1 else 0:8.4f}")

sel = [N for N in Ns if N >= Nmin]
Narr = np.array(sel, float)
d = np.array([(math.lgamma(N + 1) - pts[N][0]) / N for N in sel])
w = np.array([1.0 / max(1e-4, (pts[N][1] if pts[N][1] == pts[N][1] else 0) / N + pts[N][2] / N + 2e-4) for N in sel])
L = np.log(Narr); LL = np.log(L)

def lsq(cols, y, name):
    A = np.column_stack(cols)
    Aw = A * w[:, None]; yw = y * w
    coef, *_ = np.linalg.lstsq(Aw, yw, rcond=None)
    r = y - A @ coef
    print(f"  {name:38s} coef={np.array2string(coef, precision=4)}  rms={np.sqrt(np.mean(r ** 2)):.4f}  "
          f"chi2/dof={np.sum((r * w) ** 2) / max(1, len(y) - len(coef)):.2f}")
    return coef, r

print(f"\nfits of d(N), N >= {Nmin} ({len(sel)} points; weights 1/(sd/N + bias/N + 2e-4))")
lsq([L, np.ones_like(L)], d, "A: c' lnN + b")
lsq([L, np.ones_like(L), 1 / L], d, "A': c' lnN + b + e/lnN")
lsq([LL, np.ones_like(L)], d, "B: alpha lnlnN + b")
lsq([LL, np.ones_like(L), 1 / L], d, "D: alpha lnlnN + b + e/lnN")
best = None
for mu in np.linspace(-3, 6, 181):
    c, r = None, None
    A = np.column_stack([np.ones_like(L)]); y = d - np.log(L + mu)
    b = np.sum(w ** 2 * y) / np.sum(w ** 2); r = y - b
    chi = np.sum((r * w) ** 2)
    if best is None or chi < best[0]:
        best = (chi, mu, b, np.sqrt(np.mean(r ** 2)))
print(f"  C: ln(lnN + mu) + b                     mu={best[1]:.2f} b={best[2]:.4f} rms={best[3]:.4f} "
      f"chi2/dof={best[0] / max(1, len(sel) - 2):.2f}")
# C2: the Feynman-Kac form sigma = A(lnN - ln sigma) + B, i.e. d = ln(lnN - ln sigma + mu) + b with
# sigma ~ sigma_bar; use ln sigma ~ ln lnN + const (absorbed in mu): d = ln(lnN - lnlnN + mu) + b
best = None
for mu in np.linspace(-3, 8, 221):
    arg = L - LL + mu
    if np.any(arg <= 0):
        continue
    y = d - np.log(arg); b = np.sum(w ** 2 * y) / np.sum(w ** 2); r = y - b
    chi = np.sum((r * w) ** 2)
    if best is None or chi < best[0]:
        best = (chi, mu, b, np.sqrt(np.mean(r ** 2)))
print(f"  C2: ln(lnN - lnlnN + mu) + b            mu={best[1]:.2f} b={best[2]:.4f} rms={best[3]:.4f} "
      f"chi2/dof={best[0] / max(1, len(sel) - 2):.2f}")
# predictions at larger N from each model (fitted on the selected points)
def pred_table(Ns_new):
    out = {}
    for name, cols in [("A'", lambda L_: [L_, np.ones_like(L_), 1 / L_]),
                       ("B", lambda L_: [np.log(L_), np.ones_like(L_)]),
                       ("D", lambda L_: [np.log(L_), np.ones_like(L_), 1 / L_])]:
        A = np.column_stack(cols(L)); coef, *_ = np.linalg.lstsq(A * w[:, None], d * w, rcond=None)
        Ln = np.log(np.array(Ns_new, float)); out[name] = np.column_stack(cols(Ln)) @ coef
    return out
if '-pred' in sys.argv:
    newN = [4096, 8192, 2 ** 16, 2 ** 20]
    pt = pred_table(newN)
    print("  predicted d(N):", {k: np.round(v, 4).tolist() for k, v in pt.items()}, "at", newN)

# sigma_J at t = 1/2 from diagnostics
sig = {}; dpred = {}
for fn in glob.glob('runs/d_*_*_*.txt'):
    N, P, s = map(int, re.findall(r'd_(\d+)_(\d+)_(\d+)', fn)[0])
    rows = [dict((t.split('=')[0], t.split('=')[1]) for t in l.split()) for l in open(fn)]
    if not rows or float(rows[-1]['t']) < 0.98:
        continue
    half = [float(r['sdJ']) for r in rows if abs(float(r['t']) - 0.5) < 0.5 / 64]
    lt = [math.log(math.sqrt(2 * math.pi) * float(r['sdJ'])) for r in rows if 0 < float(r['t']) < 0.99 and float(r['sdJ']) > 0]
    lf = [-math.log(float(r['frac'])) for r in rows if 0 < float(r['t']) < 0.99]
    if N not in sig or P > sig[N][0]:
        sig[N] = (P, [], [], [])
    if P == sig[N][0]:
        sig[N][1].append(half[0]); sig[N][2].append(sum(lt) / len(lt)); sig[N][3].append(sum(lf) / len(lf))
print("\nsigma_J(t=1/2) and the local-CLT prediction of d(N):")
print(f"{'N':>5} {'P':>6} {'runs':>4} {'sigma':>7} {'mean ln(sqrt(2pi)sig)':>22} {'mean -ln frac':>14}")
SN = sorted(sig)
for N in SN:
    P, h, lt, lf = sig[N]
    print(f"{N:5d} {P:6d} {len(h):4d} {np.mean(h):7.3f} {np.mean(lt):22.4f} {np.mean(lf):14.4f}")
sN = np.array([N for N in SN if N >= Nmin], float); sv = np.array([np.mean(sig[int(N)][1]) for N in sN])
Ls = np.log(sN)
def fit_s(cols, y, name, tr=lambda v: v):
    A = np.column_stack(cols); coef, *_ = np.linalg.lstsq(A, y, rcond=None)
    pred = tr(A @ coef); r = sv - pred
    print(f"  {name:34s} coef={np.array2string(coef, precision=4)}  rms={np.sqrt(np.mean(r ** 2)):.4f}")
    return coef
print(f"fits of sigma_J(1/2), N >= {Nmin}:")
fit_s([Ls, np.ones_like(Ls)], sv, "s1: a lnN + b")
fit_s([Ls - np.log(sv), np.ones_like(Ls)], sv, "s2: A(lnN - ln sigma) + B")
fit_s([Ls, np.ones_like(Ls)], np.log(sv), "s3: ln sigma = g lnN + lnC", np.exp)
fit_s([np.log(Ls), np.ones_like(Ls)], np.log(sv), "s4: ln sigma = beta lnlnN + lnC", np.exp)
print("local slopes d sigma / d lnN:", " ".join(f"{(sv[i + 1] - sv[i]) / (Ls[i + 1] - Ls[i]):.3f}" for i in range(len(sv) - 1)))

# effective sigma: exp(mean_t ln sigma_J(t)) (this is what enters d(N)), largest P, runs averaged
print("\neffective sigma_bar = exp(mean_t ln sigma_J):")
sb = {}
for N in SN:
    P, h, lt, lf = sig[N]
    sb[N] = math.exp(np.mean(lt)) / math.sqrt(2 * math.pi)
SNs = [N for N in SN if N >= Nmin]
x = np.log(np.array(SNs, float)); y = np.array([sb[N] for N in SNs])
for i, N in enumerate(SNs):
    sl = (y[i + 1] - y[i]) / (x[i + 1] - x[i]) if i + 1 < len(SNs) else float('nan')
    print(f"  N={N:5d} P={sig[N][0]:6d} sigma_bar={y[i]:.4f}  slope to next={sl:.3f}  local power={sl / y[i]:.3f}"
          f"  local (lnN)^beta={sl * x[i] / y[i]:.3f}")
for name, A, yy, tr in [("lin a lnN + b", np.c_[x, np.ones_like(x)], y, lambda v: v),
                        ("A(lnN - ln s) + B", np.c_[x - np.log(y), np.ones_like(x)], y, lambda v: v),
                        ("power C N^g", np.c_[x, np.ones_like(x)], np.log(y), np.exp),
                        ("C (lnN)^beta", np.c_[np.log(x), np.ones_like(x)], np.log(y), np.exp),
                        ("a sqrt(lnN) + b", np.c_[np.sqrt(x), np.ones_like(x)], y, lambda v: v)]:
    c, *_ = np.linalg.lstsq(A, yy, rcond=None); r = y - tr(A @ c)
    print(f"  {name:20s} coef={np.array2string(c, precision=4)} rms={np.sqrt(np.mean(r ** 2)):.4f}"
          f"  resid={np.array2string(r, precision=3)}")
