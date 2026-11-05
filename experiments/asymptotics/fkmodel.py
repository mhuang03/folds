"""Gaussian Feynman-Kac model of section 2.3 (NOTES.txt), with the doubling-chain coupling.

Dynamic variables: the Fourier modes S^(n), n >= 1, each kicked by an independent unit complex
amount per step (adding a point x adds e(-n x/N)).  Path weight prod_k sigma_J(k)^{-1},
linearised: exp(-sum_k sum_n c_n |Delta_n|^2), Delta_n = S^(n/2)[n even] - S^(n),
c_n = 1/(pi n s)^2, s = sigma_J.  Per doubling chain n0, 2n0, 4n0, ... the potential is v^T K v
with K = sum_i c_i d_i d_i^T; the Feynman-Kac stationary state is exp(-2 v^T sqrt(K) v) per real
component, and self-consistency var J = s^2 becomes
      sum over chains of tr sqrt(K~) = s,      K~ = K at s = 1,
summed over the modes that can equilibrate (n up to n* ~ N/(pi s)).  This script prints
tr sqrt(K~) for frequency cutoffs M: it grows like 0.345 ln M, so the model predicts
      sigma_J = 0.345 (ln N - ln sigma_J) + const       (single modes, no chain coupling: 1/pi).
The fitted coefficient on the SMC data is about 0.64 (fit2.py): same law, constant ~2x larger.
"""
import math
import numpy as np


def trsqrt(M):
    tot = 0.0
    for n0 in range(1, M + 1, 2):
        ns = []; n = n0
        while n <= M:
            ns.append(n); n *= 2
        L = len(ns); K = np.zeros((L, L))
        for i, n in enumerate(ns):
            d = np.zeros(L); d[i] = -1
            if i > 0:
                d[i - 1] = 1
            K += np.outer(d, d) / (math.pi * n) ** 2
        w = np.linalg.eigvalsh(K)
        tot += np.sqrt(np.clip(w, 0, None)).sum()
    return tot


prev = None
for M in [64, 128, 256, 512, 1024, 2048, 4096]:
    t = trsqrt(M)
    print(M, round(t, 4), '' if prev is None else f"slope per ln M: {(t - prev) / math.log(2):.4f}")
    prev = t
print("single-mode (no chain coupling) slope 1/pi =", round(1 / math.pi, 4))
