"""reduced_mc.py: Monte Carlo volumes of the reduced problems of PROOFS.txt section 6 (f <= 4).
orbit / chain 1 0^(n-1): f points in (1/2, 1), field c(z) = floor(log2 1/(2z - 1));
chain 1^n:               f points in (0, 1/2), field c3(z) = 1 - #{t >= 2 : z > 1/2 - 2^-t};
valid iff c(z_i) + sum_{j<i} sign(z_j -> z_i) = 0 for every i (time order)."""
import math
import numpy as np

rng = np.random.default_rng(1)


def sgn(x, c):
    return np.where((x < c) & (c < (1 + x) / 2), 1, np.where((x / 2 < c) & (c < x), -1, 0))


def field_orbit(z):
    return np.floor(np.log2(1 / (2 * z - 1)))


def field_w3(z):
    t = np.arange(2, 60)
    return 1 - (z[..., None] > 0.5 - 2.0 ** (-t)).sum(-1)


for name, lo, hi, field in (('orbit/W1', 0.5, 1.0, field_orbit), ('W3', 0.0, 0.5, field_w3)):
    for f in (1, 2, 3, 4):
        S = 2_000_000
        z = rng.uniform(lo, hi, size=(S, f))
        ok = np.ones(S, bool)
        for i in range(f):
            s = field(z[:, i]).astype(int)
            for j in range(i):
                s = s + sgn(z[:, j], z[:, i])
            ok &= (s == 0)
        p = ok.mean()
        vol = p * (hi - lo) ** f
        err = math.sqrt(p * (1 - p) / S) * (hi - lo) ** f
        print(f'{name:9s} f={f}: vol V_f = {vol:.6f} +- {err:.6f}   vol/f! = {vol / math.factorial(f):.6f}',
              flush=True)
