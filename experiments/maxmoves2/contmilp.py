"""contmilp.py -- exact continuum maximum of the valid measure for fixed s (MILP, HiGHS).
Points 0 <= x_1 <= ... <= x_s <= 1 (multiset), F the counting function, valid set
{t : F(2t) = 2F(t)} = union_k [x_k, x_{k+1}] cap [y_{2k}/2, y_{2k+1}/2] with y the breakpoints
of F on [0, 2] (as in ../maxmoves/contopt.py).  usage: python3 contmilp.py s [s ...]"""
import sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

def solve(s):
    # variables: x_1..x_s (idx 0..s-1), v_0..v_s (idx s..2s), d_0..d_s (idx 2s+1..3s+1)
    nv = 3 * s + 2
    X = lambda i: i - 1
    V = lambda k: s + k
    D = lambda k: 2 * s + 1 + k
    def xform(j):            # x_j as (coeff dict, const), j in 0..s+1
        if j == 0: return {}, 0.0
        if j == s + 1: return {}, 1.0
        return {X(j): 1.0}, 0.0
    def yform(j):            # y_j / 2
        if j == 0: return {}, 0.0
        if j <= s: return {X(j): 0.5}, 0.0
        if j <= 2 * s: return {X(j - s): 0.5}, 0.5
        return {}, 1.0
    rows, lo, hi = [], [], []
    def add(coef, l, u):
        r = np.zeros(nv)
        for i, c in coef.items(): r[i] += c
        rows.append(r); lo.append(l); hi.append(u)
    for j in range(1, s):    # sorted
        add({X(j + 1): 1, X(j): -1}, 0, np.inf)
    for k in range(s + 1):
        ups = [xform(k + 1), yform(2 * k + 1)]
        lows = [xform(k), yform(2 * k)]
        for (cu, ku) in ups:
            for (cl, kl) in lows:
                # v_k <= up - low + (1 - d_k) * 2
                coef = {V(k): 1.0, D(k): 2.0}
                for i, c in cu.items(): coef[i] = coef.get(i, 0) - c
                for i, c in cl.items(): coef[i] = coef.get(i, 0) + c
                add(coef, -np.inf, ku - kl + 2.0)
        add({V(k): 1.0, D(k): -1.0}, -np.inf, 0)
    c = np.zeros(nv); c[s:2 * s + 1] = -1
    integrality = np.zeros(nv); integrality[2 * s + 1:] = 1
    lb = np.zeros(nv); ub = np.ones(nv)
    res = milp(c, constraints=LinearConstraint(np.array(rows), lo, hi), integrality=integrality,
               bounds=Bounds(lb, ub))
    return -res.fun, sorted(res.x[:s])

if __name__ == "__main__":
    from fractions import Fraction
    for s in map(int, sys.argv[1:]):
        val, xs = solve(s)
        print("s=%d sup=%.6f ~ %s  x=%s" % (s, val, Fraction(val).limit_denominator(200),
              np.round(xs, 4)))
