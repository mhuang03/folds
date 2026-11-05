"""Quenched Gaussian resummation at large N: Q(N) = E[-1/2 log det(Gamma o B(t))], t iid arcsine.
(The annealed y_G = log E[det^-1/2] is >= Q and was within ~7% of it for N <= 160.)"""
import numpy as np
from gauss_mc import gram

rng = np.random.default_rng(5)
for N in (40, 80, 160, 320, 640, 1280):
    Gam = gram(N)
    v = []
    for _ in range(max(4, 3200 // N)):
        t = np.sin(np.pi * rng.random(Gam.shape[0]) / 2) ** 2
        C = np.minimum.outer(t, t) - np.outer(t, t)
        s = np.sqrt(t * (1 - t))
        M = Gam * C / np.outer(s, s)
        v.append(-0.5 * np.linalg.slogdet(M)[1])
    q = np.mean(v)
    print("%5d Q=%9.2f (sd %.2f)  Q/N=%.4f  Q/(N lnN)=%.4f" % (N, q, np.std(v), q / N, q / (N * np.log(N))), flush=True)
