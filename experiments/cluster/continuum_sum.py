"""Continuum prediction for the pair sum: sum_{m<m'} kappa ~ C2 N^2 with
C2 = int int_{x<x'} K(gamma(x,x')) dx dx',  gamma = <a_m, a_m'> / (2 sqrt(r r')).
Tabulates K on a grid (continuum.K), then sums over all pairs of a large strip."""
import numpy as np
import mpmath as mp
from continuum import K

mp.mp.dps = 12
grid = np.linspace(0, 1, 26)
tab = np.array([float(K(g)) if g < 1 else float(K(0.9999)) for g in grid])
print("K table:", " ".join("%.3f:%.5f" % (g, k) for g, k in zip(grid, tab)))
print("c1 = 1/2 - 4/pi^2 =", 0.5 - 4 / np.pi ** 2, " K(0.2)/0.04 =", tab[5] / 0.04)


def gamma_matrix(N):
    M = [m for m in range(1, N + 1) if min(m - 1, N - m) >= 1]
    A = np.zeros((len(M), N))
    for i, m in enumerate(M):
        r = min(m - 1, N - m)
        A[i, m - 1 - r:m - 1] = 1
        A[i, m:m + r] = -1
    G = A @ A.T
    d = np.sqrt(np.diag(G))
    return G / np.outer(d, d)


for N in (100, 200, 400, 800):
    Gm = gamma_matrix(N)
    iu = np.triu_indices(Gm.shape[0], 1)
    g = np.abs(Gm[iu])
    S = np.interp(g, grid, tab).sum()
    print("N=%d  sum_pairs K(gamma) = %.3f   /N^2 = %.6f   frac pairs gamma>0: %.3f  mean gamma^2 = %.4f" % (
        N, S, S / N ** 2, np.mean(g > 0), np.mean(g ** 2)))
