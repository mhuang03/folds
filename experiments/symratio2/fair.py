"""fair.py -- the FAIR-BIT model: t_{2M}(lift_a H) = t_M(H) / 2 (iid fair parity bits on top of
a fixed starting law t_{m0}), and r_fair(2M) = t_M^T Pi_{2M,0} t_M = 1/2 sum_q t^T Pi_{2M,q} t.
Usage: python3 fair.py m0 mmax
"""
import sys
import numpy as np
import wl
from reduced import pi_mv


def run(m0, mmax, verbose=True):
    L = wl.law(m0)
    win, t, M = L.win, L.t, m0
    rs = []
    while 2 * M <= mmax:
        _, Pt = pi_mv(2 * M, 0, win, win, t, t)
        s = t @ Pt
        win = np.vstack([2 * win, 2 * win - 1]); t = np.concatenate([t, t]) / 2
        M *= 2
        rs.append((M, s))
        if verbose:
            print(M, f"{s:.16f}", flush=True)
    return rs


if __name__ == "__main__":
    rs = run(int(sys.argv[1]), int(sys.argv[2]))
    r = np.array([s for _, s in rs]); D = np.diff(r)
    print("# D:", " ".join(f"{d:.3e}" for d in D))
    print("# ratios:", " ".join(f"{a/b:.3f}" for a, b in zip(D[:-1], D[1:])))
