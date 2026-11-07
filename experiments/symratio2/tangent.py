"""tangent.py -- linearisation of the doubling map J_m -> J_{2m} (Theorem J) along a chain.

Chain m_k = m0 * 2^k.  The exact doubling map (both halves of size m):
    B = J_m Pi_{2m,0} J_m,  r(2m) = 1^T B 1,  J_{2m} = [[0,B],[B^T,0]] / (2 r(2m)).
Forward mode: a tangent dJ at m0 (multiplicative, dJ = J o R, R symmetric, mass 0) is pushed
through; dr_k = d r(m_k).  Dense levels up to m_dense, then levels given only implicitly by
mat-vec recursion (as in ../thetaext/theta.c), so r reaches 4 * m_dense.
Usage: python3 tangent.py m0 m_dense ndir [seed]   -> prints r_k and dr_k^{(i)} for each
direction, split into complement-even and complement-odd directions.
"""
import sys, time
import numpy as np
import wl


class Dense:
    def __init__(self, J, dJ, win, m):
        self.J, self.dJ, self.win, self.m = J, dJ, win, m

    def mv(self, v):
        return self.J @ v

    def dmv(self, v, i):
        return self.dJ[i] @ v


class Implicit:
    """J_{2m} from level `lo` (size m): J v = [B v2; B^T v1] / (2 s)."""
    def __init__(self, lo):
        self.lo, self.m = lo, 2 * lo.m
        w = len(lo.win)
        self.w = w
        self.P = wl.pi_matrix(self.m, 0, lo.win, lo.win)
        self.win = np.vstack([2 * lo.win, 2 * lo.win - 1])
        t = lo.mv(np.ones(w))
        self.t_lo = t
        self.s = t @ self.P @ t
        self.ds = []
        for i in range(len(lo.dJ) if isinstance(lo, Dense) else lo.nd):
            dt = lo.dmv(np.ones(w), i)
            self.ds.append(dt @ self.P @ t + t @ self.P @ dt)
        self.nd = len(self.ds)
        self.dJ = None

    def mv(self, v):
        w, M, P = self.w, self.lo.mv, self.P
        v1, v2 = v[:w], v[w:]
        return np.concatenate([M(P @ M(v2)), M(P.T @ M(v1))]) / (2 * self.s)

    def dmv(self, v, i):
        w, M, dM, P = self.w, self.lo.mv, self.lo.dmv, self.P
        v1, v2 = v[:w], v[w:]
        a = dM(P @ M(v2), i) + M(P @ dM(v2, i))
        b = dM(P.T @ M(v1), i) + M(P.T @ dM(v1, i))
        return np.concatenate([a, b]) / (2 * self.s) - self.mv(v) * self.ds[i] / self.s


def dense_step(L):
    """L: Dense at size m -> Dense at 2m (pruned) and r(2m), dr(2m)."""
    m = L.m
    P = wl.pi_matrix(2 * m, 0, L.win, L.win)
    JP = L.J @ P
    B = JP @ L.J
    s = B.sum()
    dB = [d @ P @ L.J + JP @ d for d in L.dJ]
    ds = [x.sum() for x in dB]
    w = len(L.win)
    win = np.vstack([2 * L.win, 2 * L.win - 1])

    def big(X):
        Z = np.zeros((2 * w, 2 * w)); Z[:w, w:] = X; Z[w:, :w] = X.T; return Z
    J2 = big(B) / (2 * s)
    keep = J2.sum(axis=1) > 0
    ix = np.ix_(keep, keep)
    J2 = np.ascontiguousarray(J2[ix])
    dJ2 = [np.ascontiguousarray((big(x) / (2 * s))[ix] - J2 * dsi / s) for x, dsi in zip(dB, ds)]
    return Dense(J2, dJ2, win[keep], 2 * m), s, ds


def directions(L, ndir, rng, parity):
    """multiplicative symmetric perturbations, mass 0, complement-even (+1) or odd (-1)."""
    c = wl.complement_perm(wl.Law(L.m, L.win, L.J, 0.0))
    assert (c >= 0).all()
    out = []
    for _ in range(ndir):
        R = rng.standard_normal(L.J.shape); R = R + R.T
        R = R + parity * R[np.ix_(c, c)]
        d = L.J * R
        if parity > 0:
            d -= L.J * (d.sum() / L.J.sum())
        out.append(d)
    return out


def run(m0, mdense, ndir, seed=1, nimpl=1):
    rng = np.random.default_rng(seed)
    base = wl.law(m0)
    L0 = Dense(base.J, [], base.win, m0)
    dirs = directions(L0, ndir, rng, +1) + directions(L0, ndir, rng, -1)
    L = Dense(base.J, dirs, base.win, m0)
    rs, drs = [], []
    while L.m < mdense:
        t0 = time.time()
        L, s, ds = dense_step(L)
        rs.append((L.m, s)); drs.append(ds)
        print(f"# dense {L.m} w={len(L.win)} r={s:.15f} ({time.time()-t0:.0f}s)", file=sys.stderr)
    top = L
    for _ in range(nimpl):
        top = Implicit(top)
        rs.append((top.m, top.s)); drs.append(top.ds)
        print(f"# implicit {top.m} r={top.s:.15f}", file=sys.stderr)
    return rs, np.array(drs)


if __name__ == "__main__":
    m0, md, nd = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    nimpl = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    rs, drs = run(m0, md, nd, seed, nimpl)
    print("# m  r(m)  then dr for", nd, "complement-even and", nd, "complement-odd directions")
    for (m, s), d in zip(rs, drs):
        print(m, f"{s:.16f}", " ".join(f"{x:.6e}" for x in d))
    D = np.diff(drs, axis=0)
    print("# successive differences of dr and their ratios D_k/D_{k+1}")
    for k in range(len(D)):
        line = " ".join(f"{x:.3e}" for x in D[k])
        rat = " ".join(f"{a/b:7.3f}" for a, b in zip(D[k - 1], D[k])) if k > 0 else ""
        print(rs[k + 1][0], line, "|", rat)
