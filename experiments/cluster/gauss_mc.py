"""Gaussian (local-CLT) resummation of all correlations.

Heuristic model: conditionally on the centre times t_m, the window imbalances D_m are
jointly Gaussian with Cov(D_m, D_m') = G_mm' * (min(t,t') - t t'), G = A A^T the Gram
matrix of the role vectors (a_me = +1 left arm, -1 right arm).  With each panel's
single-site factor normalised to the exact Wallis value this gives

    a_G(N) / a_W(N) = E_{t_m iid arcsine} [ det(Gamma o B(t))^(-1/2) ],

Gamma = correlation matrix of the role vectors, B_mm' = Brownian-bridge correlation
(min(t,t') - t t') / sqrt(t(1-t) t'(1-t')).  Its second-order expansion is exactly the
continuum pair correlation K(gamma) of continuum.py.  Monte Carlo over t.
usage: gauss_mc.py Nmin Nmax samples
"""
import sys
import numpy as np
from wallis_exact import log_aW, A as AA


def gram(N):
    M = [m for m in range(1, N + 1) if min(m - 1, N - m) >= 1]
    A = np.zeros((len(M), N))
    for i, m in enumerate(M):
        r = min(m - 1, N - m)
        A[i, m - 1 - r:m - 1] = 1
        A[i, m:m + r] = -1
    G = A @ A.T
    d = np.sqrt(np.diag(G))
    return G / np.outer(d, d)


def logmean_detinvsqrt(Gam, S, rng, batch=2000):
    n = Gam.shape[0]
    vals = []
    done = 0
    while done < S:
        b = min(batch, S - done)
        t = np.sin(np.pi * rng.random((b, n)) / 2) ** 2
        mn = np.minimum(t[:, :, None], t[:, None, :])
        C = mn - t[:, :, None] * t[:, None, :]
        s = np.sqrt(t * (1 - t))
        Bm = C / (s[:, :, None] * s[:, None, :])
        M = Gam[None] * Bm
        sign, ld = np.linalg.slogdet(M)
        vals.append(-0.5 * ld)
        done += b
    v = np.concatenate(vals)
    mx = v.max()
    lm = mx + np.log(np.mean(np.exp(v - mx)))
    # crude error estimate by batches
    k = 20
    parts = np.array_split(v, k)
    lms = [mx + np.log(np.mean(np.exp(p - mx))) for p in parts]
    return lm, np.std(lms) / np.sqrt(k), np.mean(v)


if __name__ == "__main__":
    N0, N1, S = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = np.random.default_rng(1)
    print("N   y=log(a/aW)   yG=log E det^-1/2  (err)   E[-1/2 logdet]")
    for N in range(N0, N1 + 1):
        Gam = gram(N)
        lm, err, ml = logmean_detinvsqrt(Gam, S, rng)
        y = np.log(float(AA[N - 1])) - log_aW(N) if N <= len(AA) else float("nan")
        print("%3d %9.4f %9.4f (%.4f) %9.4f" % (N, y, lm, err, ml), flush=True)
