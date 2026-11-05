"""lib.py: helpers for live5 (window arithmetic, greedy checks, ctypes exact solver)."""
import ctypes
import os

_here = os.path.dirname(os.path.abspath(__file__))
_so = os.path.join(_here, 'solver.so')
if not os.path.exists(_so) or os.path.getmtime(_so) < os.path.getmtime(os.path.join(_here, 'solver.c')):
    os.system(f'gcc -O2 -shared -fPIC -o {_so} {os.path.join(_here, "solver.c")}')
_lib = ctypes.CDLL(_so)


def reach(N, m):
    return min(m - 1, N - m)


def imb(N, S, m):
    """I_S(m) = |S n L(m)| - |S n R(m)|."""
    r = reach(N, m)
    return sum(1 for x in S if m - r <= x < m) - sum(1 for x in S if m < x <= m + r)


def solve(N, bg, tg, key=None):
    """Exact: order the target panels on the background (others absent); None if impossible."""
    A = ctypes.c_int * (N + 2)
    b, t, k = A(), A(), A()
    for x in bg:
        b[x] = 1
    for x in tg:
        t[x] = 1
    for x in range(N + 2):
        k[x] = key(x) if key else x
    out = (ctypes.c_int * 64)()
    r = _lib.solve(N, b, t, k, out)
    if r == -1:
        raise ValueError('target too large')
    if r == 0:
        return None
    return [out[i] for i in range(len(list(tg)))]


def check_bg(N, bg, order):
    """Every step balanced on the background + earlier steps."""
    S = set(bg)
    for m in order:
        if imb(N, S, m) != 0:
            return False
        S.add(m)
    return True


def coreach(N, D):
    D = set(D)
    return solve(N, D, [x for x in range(1, N + 1) if x not in D]) is not None
