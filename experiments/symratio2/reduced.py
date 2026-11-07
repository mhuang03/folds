"""reduced.py -- the MARGINAL-ONLY (block-product) model of the doubling recursion.

Replace J_M by its block-product approximation Jhat_M = 2 (t_0 t_1^T + t_1 t_0^T)
(t_p = head law restricted to first-entry parity p; exact masses 1/2 each).  Then the doubling
recursion closes on the head law t alone:
    s = t^T P t  (= r(2M)),   P = Pi_{2M,0} on W_M x W_M,
    t_{2M}(lift_0 H) = Jhat (P t)(H) / (2 s),   t_{2M}(lift_1 G) = Jhat (P^T t)(G) / (2 s).
So t_{2M}(lift_a H) = t(H) * w_{a, par H}: a 2-bit (Markov) reweighting.
Usage: python3 reduced.py m0 mmax [full]   (start from the exact t_{m0}; `full` = also exact r)
"""
import sys, ctypes
import numpy as np
import wl

wl._lib.pi_mv.restype = None
wl._lib.pi_mv.argtypes = [ctypes.c_int] * 3 + [ctypes.c_void_p, ctypes.c_int] + [ctypes.c_void_p] * 5


def pi_mv(N, q, Dwin, Cwin, a, b):
    Dwin = np.ascontiguousarray(Dwin, dtype=np.int32); Cwin = np.ascontiguousarray(Cwin, dtype=np.int32)
    a = np.ascontiguousarray(a, dtype=np.float64); b = np.ascontiguousarray(b, dtype=np.float64)
    oT = np.empty(len(Cwin)); oN = np.empty(len(Dwin))
    wl._lib.pi_mv(N, q, len(Dwin), Dwin.ctypes.data, len(Cwin), Cwin.ctypes.data,
                  a.ctypes.data, b.ctypes.data, oT.ctypes.data, oN.ctypes.data)
    return oT, oN


def jhat_mv(t, par, v):
    t0 = np.where(par == 0, t, 0.0); t1 = t - t0
    return 2 * (t0 * (t1 @ v) + t1 * (t0 @ v))


def step(win, t, M):
    par = win[:, 0] % 2
    PTt, Pt = pi_mv(2 * M, 0, win, win, t, t)
    s = t @ Pt
    a = jhat_mv(t, par, Pt); b = jhat_mv(t, par, PTt)
    t2 = np.concatenate([a, b]) / (2 * s)
    win2 = np.vstack([2 * win, 2 * win - 1])
    keep = t2 > 0
    return win2[keep], t2[keep], s


def run(m0, mmax):
    L = wl.law(m0)
    win, t, M = L.win, L.t, m0
    out = []
    while 2 * M <= mmax:
        win, t, s = step(win, t, M)
        M *= 2
        out.append((M, s))
        print(M, f"{s:.16f}", len(win), flush=True)
    return out


if __name__ == "__main__":
    out = run(int(sys.argv[1]), int(sys.argv[2]))
    rs = np.array([s for _, s in out])
    D = np.diff(rs)
    print("# D:", " ".join(f"{d:.3e}" for d in D))
    print("# ratios:", " ".join(f"{a/b:.3f}" for a, b in zip(D[:-1], D[1:])))
