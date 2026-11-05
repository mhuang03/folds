"""Aggregated LP certificates.  Find w >= 0 with  sum_m w(m) D_m(c) > 0  for EVERY labelling
c : [N] -> {0..t-1}, where D_m(c) = #{x in L(m): c(x) <= c(m)} - #{x in R(m): c(x) < c(m)}.
Such w proves that no admissible labelling exists (an admissible one has all D_m <= 0).

Pair form: sum_m w(m) D_m(c) = sum_{x<y} gamma(x,y) [c(x) <= c(y)] - sum_x w(x) r(x),
   gamma(x,y) = w(y) [y-x <= r(y)] + w(x) [y-x <= r(x)].
So w certifies iff every t-labelling has weighted non-inversion  > sum_x w(x) r(x).

Method: constraint generation.  Master LP: maximise delta, sum w = 1, w >= 0,
sum_m w(m) D_m(c) >= delta for c in the pool.  Pricing: min_c sum w D(c) as a MILP (HiGHS).
usage: lpcert.py N t [--sym]   (--sym: impose w(m) = w(M-m))"""
import sys, numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

def r_(N, m): return min(m - 1, N - m)

def Dvec(N, c):
    out = []
    for m in range(1, N + 1):
        r = r_(N, m); v = c[m - 1]
        out.append(sum(c[x - 1] <= v for x in range(m - r, m)) - sum(c[x - 1] < v for x in range(m + 1, m + r + 1)))
    return np.array(out, dtype=float)

def pricing(N, t, w):
    """minimise sum_x<y gamma [c(x) <= c(y)]  over labellings; returns (value - B, c)"""
    pairs = []
    for x in range(1, N + 1):
        for y in range(x + 1, N + 1):
            g = (w[y - 1] if y - x <= r_(N, y) else 0) + (w[x - 1] if y - x <= r_(N, x) else 0)
            if g > 1e-12: pairs.append((x, y, g))
    B = sum(w[x - 1] * r_(N, x) for x in range(1, N + 1))
    # variables: z[m,v] = [c(m) <= v], v = 0..t-2 ; p for pairs
    nz = N * (t - 1)
    def zi(m, v): return (m - 1) * (t - 1) + v
    nv = nz + len(pairs)
    cost = np.zeros(nv)
    rows, lo, hi = [], [], []
    def row(d, l, h):
        a = np.zeros(nv)
        for k, val in d.items(): a[k] += val
        rows.append(a); lo.append(l); hi.append(h)
    for m in range(1, N + 1):
        for v in range(t - 2):
            row({zi(m, v): 1, zi(m, v + 1): -1}, -np.inf, 0)
    for k, (x, y, g) in enumerate(pairs):
        pk = nz + k; cost[pk] = g
        for v in range(t):
            # p >= [c(x) <= v] - [c(y) <= v-1]
            d = {pk: 1}; rhs = 0
            if v <= t - 2: d[zi(x, v)] = d.get(zi(x, v), 0) - 1
            else: rhs += 1
            if v - 1 >= 0: d[zi(y, v - 1)] = d.get(zi(y, v - 1), 0) + 1
            row(d, rhs, np.inf)
    integrality = np.array([1] * nz + [0] * len(pairs))
    bounds = Bounds(np.zeros(nv), np.ones(nv))
    cons = LinearConstraint(np.array(rows), lo, hi) if rows else None
    res = milp(cost, constraints=cons, integrality=integrality, bounds=bounds)
    z = res.x
    c = []
    for m in range(1, N + 1):
        c.append(next((v for v in range(t - 1) if z[zi(m, v)] > 0.5), t - 1))
    return res.fun - B, c

def run(N, t, sym=False, verbose=False):
    M = N + 1
    pool = []
    # seeds
    pool.append([0] * N); pool.append([t - 1] * N)
    w = np.ones(N) / N
    for it in range(500):
        A = np.array([Dvec(N, c) for c in pool])
        # maximise delta: vars (w, delta)
        nvar = N + 1
        cobj = np.zeros(nvar); cobj[-1] = -1
        A_ub = np.hstack([-A, np.ones((len(pool), 1))]); b_ub = np.zeros(len(pool))
        A_eq = [np.r_[np.ones(N), 0]]; b_eq = [1]
        if sym:
            for m in range(1, N + 1):
                if m < M - m:
                    a = np.zeros(nvar); a[m - 1] = 1; a[M - m - 1] = -1; A_eq.append(a); b_eq.append(0)
        res = linprog(cobj, A_ub=A_ub, b_ub=b_ub, A_eq=np.array(A_eq), b_eq=b_eq,
                      bounds=[(0, None)] * N + [(None, None)], method='highs')
        w = res.x[:N]; delta = res.x[-1]
        val, c = pricing(N, t, w)
        if verbose: print(it, 'master', round(delta, 5), 'pricing', round(val, 5), ''.join(map(str, c)))
        if val >= delta - 1e-7:
            return delta, w, pool
        pool.append(c)
    return None, w, pool

if __name__ == '__main__':
    N, t = int(sys.argv[1]), int(sys.argv[2])
    delta, w, pool = run(N, t, '--sym' in sys.argv, '-v' in sys.argv)
    print(f'N={N} t={t}: best margin delta = {delta:.6f}', 'CERTIFICATE' if delta > 1e-7 else 'no certificate')
    if delta > 1e-7:
        wm = w / w[w > 1e-9].min()
        print('w (normalised to min positive = 1):', ' '.join(f'{x:.3g}' for x in wm))
