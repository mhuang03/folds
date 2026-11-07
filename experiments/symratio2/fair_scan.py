"""fair_scan.py -- the fair-bit model from every base size 9..18, with the true law t_M and
with random laws mu on W_M (random positive weights; optionally complement-symmetrised).
Prints the successive differences D_k of r_fair(M 2^k) and their ratios."""
import sys
import numpy as np
import wl
from reduced import pi_mv


def fair_chain(win, t, M, K):
    rs = []
    for _ in range(K):
        _, Pt = pi_mv(2 * M, 0, win, win, t, t)
        rs.append(t @ Pt)
        win = np.vstack([2 * win, 2 * win - 1]); t = np.concatenate([t, t]) / 2
        M *= 2
    return np.array(rs)


def show(tag, rs):
    D = np.diff(rs)
    rat = [a / b if b != 0 else np.inf for a, b in zip(D[:-1], D[1:])]
    print(tag, " D:", " ".join(f"{d: .2e}" for d in D), "| ratios:", " ".join(f"{x:.3f}" for x in rat), flush=True)


rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
K = 6
for M in range(9, 19):
    L = wl.law(M)
    show(f"M={M:2d} true  ", fair_chain(L.win, L.t, M, K))
    mu = rng.random(len(L.win)); mu /= mu.sum()
    show(f"M={M:2d} random", fair_chain(L.win, mu, M, K))
    c = wl.complement_perm(L)
    mus = mu + mu[c]; mus /= mus.sum()
    show(f"M={M:2d} rnd+C ", fair_chain(L.win, mus, M, K))
