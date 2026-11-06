"""cert3.py: Handelman certificates P = sum c_j prod_j (c >= 0) by a float LP (forms normalised to
coefficients of size 1 for conditioning) and an exact rounding: on the support S of the float
solution, the free columns of the exact system keep their (rationalised) float values, the pivot
columns are solved exactly; accepted if all >= 0.  Returns (deg, combos) or None."""
import itertools
from fractions import Fraction as F
import numpy as np
import sympy as sp
from scipy.optimize import linprog

DEBUG = False


def _prods(nforms, deg):
    out = [()]
    for k in range(1, deg + 1):
        out += list(itertools.combinations_with_replacement(range(nforms), k))
    return out


def _poly_dict(e, vars_):
    p = sp.Poly(sp.expand(e), *vars_)
    return {m: F(int(sp.Rational(c).p), int(sp.Rational(c).q)) for m, c in zip(p.monoms(), p.coeffs())}


def _mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            out[m] = out.get(m, 0) + ca * cb
    return {m: c for m, c in out.items() if c != 0}


def exact_round(Acols, b, x, S):
    """Acols: dict col -> {row: Fraction}; b: {row: Fraction}; x: float values; S: support columns."""
    rows = sorted(set(b) | set(r for j in S for r in Acols[j]))
    ri = {r: i for i, r in enumerate(rows)}
    S = list(S)
    M = [[F(0)] * len(S) for _ in rows]
    for k, j in enumerate(S):
        for r, c in Acols[j].items():
            M[ri[r]][k] = c
    rhs = [b.get(r, F(0)) for r in rows]
    # rref on M | rhs
    m, n = len(rows), len(S)
    A = [M[i][:] + [rhs[i]] for i in range(m)]
    piv = []
    rr = 0
    for col in range(n):
        p = next((i for i in range(rr, m) if A[i][col] != 0), None)
        if p is None:
            continue
        A[rr], A[p] = A[p], A[rr]
        pv = A[rr][col]
        A[rr] = [v / pv for v in A[rr]]
        for i in range(m):
            if i != rr and A[i][col] != 0:
                f = A[i][col]
                A[i] = [vi - f * vr for vi, vr in zip(A[i], A[rr])]
        piv.append(col)
        rr += 1
        if rr == m:
            break
    # consistency
    for i in range(rr, m):
        if A[i][n] != 0:
            if DEBUG:
                print('   inconsistent', float(A[i][n]), 'rank', rr, 'cols', n)
            return None
    free = [k for k in range(n) if k not in piv]
    val = {}
    for k in free:
        val[k] = max(F(0), F(x[S[k]]).limit_denominator(10 ** 9))
    for i, col in enumerate(piv):
        s_ = A[i][n] - sum(A[i][k] * val[k] for k in free)
        val[col] = s_
    if all(v >= 0 for v in val.values()):
        return {S[k]: v for k, v in val.items()}
    if DEBUG:
        print('   negative', [float(v) for v in val.values() if v < 0][:5])
    return None


def certify3(P, forms, vars_, maxdeg=4):
    Pd = _poly_dict(P, vars_)
    fd = []
    for f in forms:
        d = _poly_dict(f, vars_)
        if not d:
            continue
        fd.append(d)
    nf = len(forms)
    fdl = [_poly_dict(f, vars_) for f in forms]
    for deg in range(1, maxdeg + 1):
        combos = _prods(nf, deg)
        cols = {}
        cache = {(): {tuple([0] * len(vars_)): F(1)}}
        for cmb in combos:
            if cmb not in cache:
                cache[cmb] = _mul(cache[cmb[:-1]], fdl[cmb[-1]])
            cols[cmb] = cache[cmb]
        monos = sorted(set(Pd) | set(m for c in cols.values() for m in c))
        mi = {m: i for i, m in enumerate(monos)}
        A = np.zeros((len(monos), len(combos)))
        for j, cmb in enumerate(combos):
            for m, c in cols[cmb].items():
                A[mi[m], j] = float(c)
        b = np.zeros(len(monos))
        for m, c in Pd.items():
            b[mi[m]] = float(c)
        rs = np.maximum(np.abs(A).max(axis=1), np.abs(b))
        rs[rs == 0] = 1
        As, bs = A / rs[:, None], b / rs
        cs = np.abs(As).max(axis=0)
        cs[cs == 0] = 1
        As = As / cs[None, :]
        for cost in (np.ones(len(combos)), np.array([1.0 + len(c) for c in combos])):
            res = linprog(cost, A_eq=As, b_eq=bs, bounds=[(0, None)] * len(combos), method='highs')
            if res.status != 0:
                if DEBUG:
                    print('deg', deg, 'LP status', res.status)
                break
            x = res.x / cs
            S = [j for j in range(len(combos)) if res.x[j] > 1e-11]
            S_lin = [j for j, c in enumerate(combos) if len(c) <= 1]
            if DEBUG:
                print('deg', deg, 'support', len(S))
            S = sorted(S, key=lambda j: -x[j])
            S_2 = [j for j, c in enumerate(combos) if len(c) <= 2 and j not in S]
            for SS in (S, S + [j for j in S_lin if j not in S], S + S_2):
                r = exact_round({j: {mi[m]: c for m, c in cols[combos[j]].items()} for j in SS},
                                {mi[m]: c for m, c in Pd.items()}, x, SS)
                if r is not None:
                    return deg, [combos[j] for j in sorted(r) if r[j] != 0]
            # interior point on S + S_2: maximise t with c_j >= t (j in S)
            SS = S + S_2
            k = len(SS)
            Asub = As[:, SS]
            # variables c (k), t ; constraint Asub c = bs ; -c_j + t <= 0 for j < len(S)
            Aub = np.zeros((len(S), k + 1))
            for i in range(len(S)):
                Aub[i, i] = -1.0
                Aub[i, k] = 1.0
            r2 = linprog(np.r_[np.zeros(k), -1.0], A_ub=Aub, b_ub=np.zeros(len(S)),
                         A_eq=np.hstack([Asub, np.zeros((Asub.shape[0], 1))]), b_eq=bs,
                         bounds=[(0, None)] * k + [(0, 1e3)], method='highs')
            if r2.status == 0 and r2.x[k] > 0:
                x2 = np.zeros(len(combos))
                x2[SS] = r2.x[:k] / cs[SS]
                SS2 = sorted(SS, key=lambda j: -x2[j])
                r = exact_round({j: {mi[m]: c for m, c in cols[combos[j]].items()} for j in SS2},
                                {mi[m]: c for m, c in Pd.items()}, x2, SS2)
                if r is not None:
                    return deg, [combos[j] for j in sorted(r) if r[j] != 0]
    return None
