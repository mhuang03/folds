"""Continuum (local-CLT) limit of the pair correlation.

For windows of macroscopic size (radii rho N, rho' N), conditionally on the two centre
times t, t' the window imbalances (D1, D2) are approximately Gaussian with
  Var D1 = 2 rho N t(1-t),  Var D2 = 2 rho' N t'(1-t'),  Cov = N sigma (min(t,t') - t t'),
where sigma = int a(z) b(z) dz is the signed overlap of the two role functions
(a = +1 on the left arm, -1 on the right arm).  The local CLT gives
  kappa -> K(gamma) = (1/pi^2) int int [t(1-t)t'(1-t')]^(-1/2) (1-R^2)^(-1/2) dt dt' - 1,
  R = gamma sqrt(t(1-t')/((1-t)t'))  (t<t'),  gamma = sigma / (2 sqrt(rho rho')).
Series:  K(gamma) = sum_{k>=1} c_k gamma^(2k), c_k = binom(2k,k)/4^k * (2/pi^2) * I_k,
I_k = int int_{t<t'} t^(k-1/2) (1-t)^(-k-1/2) t'^(-k-1/2) (1-t')^(k-1/2).
"""
import sys
import mpmath as mp

mp.mp.dps = 20


def K(gamma):
    g2 = mp.mpf(gamma) ** 2
    # substitute t = sin^2(a), t' = sin^2(b): dt/sqrt(t(1-t)) = 2 da
    def f(a, b):
        if a >= b:
            return 0
        R2 = g2 * (mp.sin(a) * mp.cos(b)) ** 2 / (mp.cos(a) * mp.sin(b)) ** 2
        return 4 / mp.sqrt(1 - R2)
    v = mp.quad(lambda b: mp.quad(lambda a: f(a, b), [0, b]), [0, mp.pi / 2])
    return 2 * v / mp.pi ** 2 - 1


if __name__ == "__main__":
    for g in [0.1, 0.2, 0.3, 0.408248, 0.5, 0.7, 0.9, 0.99]:
        k = K(g)
        print("gamma=%.4f  K=%.6f  K/gamma^2=%.6f" % (g, k, k / g ** 2))
