"""wl.py -- window laws J_m (Theorem J of ../symratio/PROOFS.txt) in double precision.

J_m is stored as a dense symmetric matrix over the window set W_m (heads = reversed tails),
normalised to total mass 1.  For x >= 19 the index set is lift_0 W_{floor x/2} ++
lift_1 W_{ceil x/2} (then pruned to the windows of positive weight), and
    J_x = [[0, B0], [B0^T, 0]] / (2 r(x)),   B0 = J_fl Pi_{x,0} J_ce,
    2 r(x) = 1^T B0 1 + 1^T B1 1 (B1 = J_ce Pi_{x,1} J_fl = B0^T, checked).
"""
import os, ctypes, functools
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
os.environ.setdefault("OMP_NUM_THREADS", "2")
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
_lib = ctypes.CDLL(os.path.join(HERE, "pilib.so"))
_lib.enum_base.restype = ctypes.c_long
_lib.enum_base.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_long]
_lib.pi_dense.restype = None
_lib.pi_dense.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_void_p,
                          ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p]
THETA_SMALL = {9: 496, 10: 1066, 11: 2460, 12: 6128, 13: 12840, 14: 29380, 15: 74904,
               16: 212728, 17: 368016, 18: 659296}
BASE = 18


def pi_matrix(N, q, Dwin, Cwin):
    Dwin = np.ascontiguousarray(Dwin, dtype=np.int32)
    Cwin = np.ascontiguousarray(Cwin, dtype=np.int32)
    out = np.empty((len(Dwin), len(Cwin)), dtype=np.float64)
    _lib.pi_dense(N, q, len(Dwin), Dwin.ctypes.data, len(Cwin), Cwin.ctypes.data, out.ctypes.data)
    return out


class Law:
    def __init__(self, m, win, J, logtheta, r=None, Jraw=None):
        self.m, self.win, self.J, self.logtheta, self.r = m, win, J, logtheta, r
        self.Jraw = Jraw          # integer counts (base sizes only)

    @property
    def t(self):
        return self.J.sum(axis=1)


def base_law(m):
    cap = THETA_SMALL[m]
    H = np.empty(cap * 6, dtype=np.int32); T = np.empty(cap * 6, dtype=np.int32)
    n = _lib.enum_base(m, H.ctypes.data, T.ctypes.data, cap)
    assert n == cap, (m, n)
    H = H.reshape(-1, 6); T = T.reshape(-1, 6)
    win, hi = np.unique(H, axis=0, return_inverse=True)
    key = {tuple(w): i for i, w in enumerate(win)}
    ti = np.array([key[tuple(g)] for g in T])
    Jc = np.zeros((len(win), len(win)))
    np.add.at(Jc, (hi.ravel(), ti), 1.0)
    assert np.allclose(Jc, Jc.T)
    return Law(m, win, Jc / n, np.log(n), Jraw=Jc)


@functools.lru_cache(maxsize=None)
def law(x):
    if x <= BASE:
        return base_law(x)
    A, Bl = law(x // 2), law((x + 1) // 2)
    P0 = pi_matrix(x, 0, A.win, Bl.win)
    P1 = pi_matrix(x, 1, Bl.win, A.win)
    B0 = A.J @ P0 @ Bl.J
    B1 = Bl.J @ P1 @ A.J
    err = np.abs(B1 - B0.T).max()
    assert err < 1e-12 * max(1.0, B0.max()), (x, err)
    two_r = B0.sum() + B1.sum()
    win = np.vstack([2 * A.win - 0, 2 * Bl.win - 1])
    w0 = len(A.win)
    J = np.zeros((len(win), len(win)))
    J[:w0, w0:] = B0
    J[w0:, :w0] = B0.T
    J /= two_r
    keep = J.sum(axis=1) > 0
    J = np.ascontiguousarray(J[np.ix_(keep, keep)])
    return Law(x, win[keep], J, A.logtheta + Bl.logtheta + np.log(two_r), r=two_r / 2)


def r_of(n):
    """r(n) from the marginals at floor/ceil n/2 (no J_n needed)."""
    A, Bl = law(n // 2), law((n + 1) // 2)
    tA, tB = A.t, Bl.t
    s = tA @ pi_matrix(n, 0, A.win, Bl.win) @ tB + tB @ pi_matrix(n, 1, Bl.win, A.win) @ tA
    return s / 2


def complement_perm(L):
    """index permutation of W_m induced by v -> m+1-v (valid on heads for any m)."""
    key = {tuple(w): i for i, w in enumerate(L.win)}
    c = L.m + 1 - L.win
    return np.array([key.get(tuple(w), -1) for w in c])
