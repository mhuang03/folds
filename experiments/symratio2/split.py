"""split.py -- split the doubling defect r(2N) - r(N) into a part seen by the block-product
approximation of J_{N/2} and a correlation part.

M = N/2.  J_M = J^(0) + J^(1) (head parity p blocks).  Jhat^(p) = (J^(p) 1)(1^T J^(p)) / mass.
t_N from J_M (exact) or from Jhat_M (approx), then r(2N) = 1/2 sum_q t_N^T Pi_{2N,q} t_N.
Prints N, r(N), r(2N), Lin = rhat(2N) - r(N), Cor = r(2N) - rhat(2N), kappa(M).
"""
import sys
import numpy as np
import wl


def blocks(L):
    """index masks of head parity 0 / 1 in W_M."""
    par = L.win[:, 0] % 2
    return [par == 0, par == 1]


def t_next(L, Jm, N):
    """t_N (over I_N = lift_0 W_M ++ lift_1 W_M) from J_M := Jm (both halves size M)."""
    t = Jm.sum(axis=1)
    P0 = wl.pi_matrix(N, 0, L.win, L.win)
    s = t @ P0 @ t
    a = Jm @ (P0 @ t)        # rows: lift_0 heads  (B 1)
    b = Jm @ (P0.T @ t)      # lift_1 part        (B^T 1)
    return np.concatenate([a, b]) / (2 * s), s


def r2(L, Jm, N):
    tN, rN = t_next(L, Jm, N)
    win = np.vstack([2 * L.win, 2 * L.win - 1])
    P = wl.pi_matrix(2 * N, 0, win, win)
    return tN @ P @ tN, rN


def main(chain):
    for M in chain:
        L = wl.law(M)
        N = 2 * M
        J = L.J
        Jh = np.zeros_like(J)
        kap = 0.0
        for msk in blocks(L):
            B = J * msk[:, None]
            mass = B.sum()
            if mass == 0:
                continue
            Bh = np.outer(B.sum(axis=1), B.sum(axis=0)) / mass
            Jh += Bh
            kap += np.abs(B - Bh).sum()
        rex, rN = r2(L, J, N)
        rh, _ = r2(L, Jh, N)
        print(N, f"{rN:.15f} {rex:.15f}  Lin={rh - rN: .3e}  Cor={rex - rh: .3e}  kappa(M)={kap:.3e}", flush=True)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]])
