"""handel.py: Handelman-type positivity certificates by LP.

Given a polynomial P (sympy) and linear forms l_1..l_m (sympy, assumed >= 0 on the region),
find c >= 0 with  P - sum_j c_j prod_j  having all coefficients >= 0 ... more precisely we look
for  P = sum_j c_j prod_j + s,  s >= 0 a constant,  prod_j ranging over products of at most
`deg` of the l_i (with repetition).  The support (which products) is what Lean's linarith needs.
"""
import itertools
import sympy as sp
import numpy as np
from scipy.optimize import linprog


def products(forms, deg):
    m = len(forms)
    out = [((), sp.Integer(1))]
    for k in range(1, deg + 1):
        for comb in itertools.combinations_with_replacement(range(m), k):
            e = sp.Integer(1)
            for i in comb:
                e = e * forms[i]
            out.append((comb, sp.expand(e)))
    return out


SCALE = 1000


def certify(P, forms, vars_, deg, prods=None, verbose=False, maxsupp=None, scale=None):
    """float LP in the scaled variables vars = SCALE * vars' (better conditioned)."""
    sc_ = SCALE if scale is None else scale
    sub = {x: sc_ * x for x in vars_}
    P = sp.expand(P.subs(sub))
    forms = [sp.expand(f.subs(sub)) for f in forms]
    prods = products(forms, deg) if prods is None else [(c, sp.expand(e.subs(sub))) for c, e in prods]
    polys = [sp.Poly(e, *vars_) for _, e in prods]
    Pp = sp.Poly(P, *vars_)
    monos = set(Pp.monoms())
    for p in polys:
        monos |= set(p.monoms())
    monos = sorted(monos)
    idx = {m: i for i, m in enumerate(monos)}
    A = np.zeros((len(monos), len(prods)))
    for j, p in enumerate(polys):
        for m, c in zip(p.monoms(), p.coeffs()):
            A[idx[m], j] = float(c)
    b = np.zeros(len(monos))
    for m, c in zip(Pp.monoms(), Pp.coeffs()):
        b[idx[m]] = float(c)
    # scale rows
    sc = np.maximum(np.abs(A).max(axis=1), np.abs(b))
    sc[sc == 0] = 1
    A /= sc[:, None]
    b /= sc
    # column scaling
    cs = np.abs(A).max(axis=0)
    cs[cs == 0] = 1
    A /= cs[None, :]
    # objective: prefer sparse (minimise sum c weighted by degree)
    cost = np.array([1.0 + len(c) for c, _ in prods])
    res = linprog(cost, A_eq=A, b_eq=b, bounds=[(0, None)] * len(prods), method="highs")
    if res.status != 0:
        return None
    if np.max(np.abs(A @ res.x - b)) > 1e-7 or not np.any(res.x > 1e-9):
        return None
    supp = [(prods[j][0], res.x[j] / cs[j]) for j in range(len(prods)) if res.x[j] > 1e-14]
    return supp


def exact_feasible(P, prods_sel, vars_):
    """exact (rational) check that P = sum c_j prod_j with c >= 0 for the selected products."""
    from sympy.solvers.simplex import linprog as slp
    from sympy import Matrix, Rational
    P = sp.expand(P)
    polys = [sp.Poly(e, *vars_) for _, e in prods_sel]
    Pp = sp.Poly(P, *vars_)
    monos = set(Pp.monoms())
    for p in polys:
        monos |= set(p.monoms())
    monos = sorted(monos)
    idx = {m: i for i, m in enumerate(monos)}
    A = [[0] * len(prods_sel) for _ in monos]
    for j, p in enumerate(polys):
        for m, c in zip(p.monoms(), p.coeffs()):
            A[idx[m]][j] = sp.Rational(c)
    b = [0] * len(monos)
    for m, c in zip(Pp.monoms(), Pp.coeffs()):
        b[idx[m]] = sp.Rational(c)
    try:
        val, x = slp(Matrix([1] * len(prods_sel)), A=Matrix([[0] * len(prods_sel)]), b=Matrix([0]),
                     A_eq=Matrix(A), b_eq=Matrix(b))
    except Exception:
        return None
    return x


def exact_solve(P, prods_sel, vars_):
    """exact solution of P = sum c_j prod_j on the selected products if unique; None otherwise."""
    P = sp.expand(P)
    polys = [sp.Poly(e, *vars_) for _, e in prods_sel]
    Pp = sp.Poly(P, *vars_)
    monos = set(Pp.monoms())
    for p in polys:
        monos |= set(p.monoms())
    monos = sorted(monos)
    idx = {m: i for i, m in enumerate(monos)}
    A = sp.zeros(len(monos), len(prods_sel))
    for j, p in enumerate(polys):
        for m, c in zip(p.monoms(), p.coeffs()):
            A[idx[m], j] = sp.Rational(c)
    b = sp.zeros(len(monos), 1)
    for m, c in zip(Pp.monoms(), Pp.coeffs()):
        b[idx[m], 0] = sp.Rational(c)
    try:
        sol, params = A.gauss_jordan_solve(b)
    except ValueError:
        return None
    if params.shape[0] > 0:
        sol = sol.subs({p: 0 for p in params})
    if all(x >= 0 for x in sol):
        return sol
    return None


def certify_exact(P, forms, vars_, maxdeg=4, prods_cache=None, scales=(1000, 1, 30)):
    """float LP (vertex) for a support, then exact solve on that support.
    Returns (deg, list of combs) or None."""
    if prods_cache is None:
        prods_cache = {}
    for deg in range(1, maxdeg + 1):
        if deg not in prods_cache:
            prods_cache[deg] = products(forms, deg)
        prods = prods_cache[deg]
        for sc_ in scales:
            s = certify(P, forms, vars_, deg, prods=prods, scale=sc_)
            if s is None:
                continue
            sel = set(c for c, _ in s)
            cand = [pp for pp in prods if pp[0] in sel or len(pp[0]) <= 1]
            if exact_solve(P, cand, vars_) is not None:
                return deg, [c for c, _ in cand]
    return None
