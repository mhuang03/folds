"""delta.py -- the fair-bit model in closed form, and the interaction functional Delta.

With the automaton of automaton.py, for a law mu on windows of size M (any M >= 2) and k >= 0,
    r_fair(M 2^{k+1}) = sum_state p_k(state) F_mu(state),
    F_mu(g,h) = E_{S,T ~ mu iid} Pi^{(g,h)}_M(S, T),   p_0 = (delta_{(-1,1)} + delta_{(1,-1)})/2,
    p_k = pi + 4^{-k} v / 6  for k >= 1 (Jacobsthal numbers),  v = (0,1,-1,1,-2,1,-1,1,0).
Hence r_fair(M 2^{k+1}) = Phi + 4^{-k} Delta(F_mu) / 6 for k >= 1, with
    Delta(F) = F(-1,0) + F(0,-1) + F(0,1) + F(1,0) - F(-1,1) - F(1,-1) - 2 F(0,0).
This script checks the closed form against fair.py and tabulates Delta(Pi^{.}(S,T)) per
window pair for M = 9..18: is it identically 0 when 3 | M?
"""
import ctypes, sys
import numpy as np
import wl
from fair import run as fair_run

wl._lib.pi_gh_all.restype = None
wl._lib.pi_gh_all.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p]
STATES = [(g, h) for g in (-1, 0, 1) for h in (-1, 0, 1)]
V = np.array([0, 1, -1, 1, -2, 1, -1, 1, 0], dtype=float)
PI_ST = np.array([0, 1, 2, 1, 4, 1, 2, 1, 0], dtype=float) / 12


def pi_gh(L, Dwin, Cwin):
    Dwin = np.ascontiguousarray(Dwin, dtype=np.int32); Cwin = np.ascontiguousarray(Cwin, dtype=np.int32)
    out = np.empty((len(Dwin), len(Cwin), 9), dtype=np.int32)
    wl._lib.pi_gh_all(L, len(Dwin), Dwin.ctypes.data, len(Cwin), Cwin.ctypes.data, out.ctypes.data)
    return out


def main():
    from automaton import T, idx
    for M in range(9, 19):
        L = wl.law(M)
        P = pi_gh(M, L.win, L.win)                # rows: reversed tails, cols: heads (same set)
        F = np.einsum('i,ijs,j->s', L.t, P, L.t)
        p = np.zeros(9); p[idx[(-1, 1)]] = p[idx[(1, -1)]] = 0.5
        pred = []
        for k in range(5):
            pred.append(p @ F); p = p @ T
        fr = [s for _, s in fair_run(M, M * 2 ** 5, verbose=False)]
        dl = P.astype(float) @ V                  # Delta per window pair
        nz = np.abs(dl) > 0
        print(f"M={M:2d} closed-form vs fair.py max err {max(abs(a-b) for a, b in zip(pred, fr)):.1e};"
              f" Delta(F_t)={F @ V: .3e}; #pairs with Delta != 0: {nz.sum()} of {nz.size};"
              f" values {sorted(set(dl[nz].astype(int).tolist()))[:8]}", flush=True)


if __name__ == "__main__":
    main()
