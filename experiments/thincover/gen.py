"""gen.py: slice certificates (side w1 = (1, 0)) on pieces of the thin lines, and their Lean lemmas.

A piece: Lean variables `vars` (sympy symbols, ℕ in Lean), the pair as expressions
(Nx, ux, vx) in them, linear hypotheses `hyps` (sympy linear forms >= 0 with integer coefficients),
a slice option (o, f, t, p, j) and a bottom height c0 (linear in the variables, rational coefficients),
and the active lower bounds (i0, i1) of s at c0 and c0 + 1 (indices into the slice forms: 1 or 3).

The 15 conditions of `ThinCover.sliceH` / `sliceH'` are rational functions; each is cleared
(numerator P, positive denominator D) and P >= 0 is certified on the polyhedron {hyps >= 0,
vars >= 0} by a Handelman-type LP (`../coverall/handel.py`); Lean: `nonneg_of_cleared` with
`linarith` and the product hints.
"""
import sys
import os
import pickle
import hashlib
import sympy as sp
from fractions import Fraction as F

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'coverall'))
from handel import certify, exact_solve, exact_feasible, products  # noqa: E402

CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tmp', 'lpcache.pkl')
_cache = None


def cache():
    global _cache
    if _cache is None:
        try:
            _cache = pickle.load(open(CACHE, 'rb'))
        except Exception:
            _cache = {}
    return _cache


def save_cache():
    if _cache is not None:
        os.makedirs(os.path.dirname(CACHE), exist_ok=True)
        pickle.dump(_cache, open(CACHE, 'wb'))


_prods = {}


def certify_exact2(P, forms, vars_, maxdeg=4, scales=(1000, 1, 30)):
    """float LP for a support, then an exact solve restricted to that support (falling back to
    the support plus all linear forms, then an exact LP).  Returns (deg, combos) or None."""
    for deg in range(1, maxdeg + 1):
        key = (tuple(map(str, forms)), deg)
        if key not in _prods:
            _prods[key] = products(forms, deg)
        prods = _prods[key]
        for sc_ in scales:
            try:
                s = certify(P, forms, vars_, deg, prods=prods, scale=sc_)
            except Exception:
                s = None
            if s is None:
                continue
            sel = set(c for c, _ in s)
            for cand in ([pp for pp in prods if pp[0] in sel],
                         [pp for pp in prods if pp[0] in sel or len(pp[0]) <= 1]):
                if exact_solve(P, cand, vars_) is not None:
                    return deg, [c for c, _ in cand]
            cand = [pp for pp in prods if pp[0] in sel or len(pp[0]) <= 1]
            if exact_feasible(P, cand, vars_) is not None:
                return deg, [c for c, _ in cand]
    return None


def handelman(P, forms, vars_, maxdeg=4):
    key = hashlib.sha1(repr((sp.srepr(sp.expand(P)), [sp.srepr(sp.expand(f)) for f in forms],
                             [str(v) for v in vars_], maxdeg)).encode()).hexdigest()
    c = cache()
    if key in c:
        return c[key]
    if sp.expand(P).is_number:
        r = (0, []) if sp.expand(P) >= 0 else None
    else:
        r = certify_exact2(sp.expand(P), forms, tuple(vars_), maxdeg)
    c[key] = r
    return r


# ---------------------------------------------------------------- Lean printing

def lean_poly(e, vars_):
    """integer polynomial -> Lean ℚ expression with (x : ℚ) casts."""
    e = sp.expand(e)
    if e == 0:
        return '0'
    p = sp.Poly(e, *vars_)
    terms = []
    for mon, c in zip(p.monoms(), p.coeffs()):
        c = sp.Rational(c)
        fs = []
        for var, k in zip(vars_, mon):
            if k == 1:
                fs.append('(%s : ℚ)' % var)
            elif k > 1:
                fs.append('(%s : ℚ) ^ %d' % (var, k))
        terms.append((c, ' * '.join(fs)))
    s = ''
    for i, (c, body) in enumerate(terms):
        ac = abs(c)
        cs_ = str(ac) if ac.is_Integer else '(%d / %d : ℚ)' % (ac.p, ac.q)
        if not body:
            t = cs_
        elif ac == 1:
            t = body
        else:
            t = '%s * %s' % (cs_, body)
        s = (('-' if c < 0 else '') + t) if i == 0 else s + (' - ' if c < 0 else ' + ') + t
    return s


def lean_nat(e, vars_):
    """integer-coefficient polynomial with nonnegative coefficients -> Lean ℕ expression."""
    e = sp.expand(e)
    p = sp.Poly(e, *vars_)
    terms = []
    for mon, c in zip(p.monoms(), p.coeffs()):
        c = int(c)
        assert c > 0, e
        fs = []
        for var, k in zip(vars_, mon):
            fs += [str(var)] * k
        body = ' * '.join(fs)
        terms.append(body if c == 1 and body else (str(c) if not body else '%d * %s' % (c, body)))
    return ' + '.join(terms) if terms else '0'


def nat_ineq(f, vars_):
    """linear form f >= 0 (integer coefficients) -> Lean ℕ inequality 'lhs ≤ rhs'."""
    f = sp.expand(f)
    pos = sum((t for t in sp.Add.make_args(f) if t.as_coeff_Mul()[0] > 0), sp.Integer(0))
    neg = -sum((t for t in sp.Add.make_args(f) if t.as_coeff_Mul()[0] < 0), sp.Integer(0))
    return '%s ≤ %s' % (lean_nat(neg, vars_) if neg != 0 else '0', lean_nat(pos, vars_) if pos != 0 else '0')


def lean_rat(e, vars_):
    """rational function -> '(num) / (den)' (or the polynomial)."""
    e = sp.together(sp.expand(e))
    n, d = sp.fraction(e)
    n, d = sp.expand(n), sp.expand(d)
    if d == 1:
        return '(%s)' % lean_poly(n, vars_)
    return '(%s) / (%s)' % (lean_poly(n, vars_), lean_poly(d, vars_))


def clear_int(e):
    """make the linear form e have integer coefficients (scale by the lcm of denominators)."""
    e = sp.expand(e)
    den = 1
    for t in sp.Add.make_args(e):
        den = sp.ilcm(den, sp.fraction(t.as_coeff_Mul()[0])[1])
    return sp.expand(e * den)


# ---------------------------------------------------------------- the slice conditions

def family(f, Nx, y):
    if f == 0:
        return dict(K=Nx + 2, R=y, al=0, be=1, S=(Nx + 1) / sp.Integer(2), amin=2,
                    smax='(%s + 2) / 2', Sdesc='Z')
    if f == 1:
        return dict(K=Nx, R=y - 2, al=0, be=1, S=Nx / sp.Integer(2), amin=1, smax='(%s + 1) / 2')
    return dict(K=Nx, R=y - 2, al=1, be=0, S=(Nx - 1) / sp.Integer(2), amin=2, smax='%s / 2')


def slice_forms(opt, Nx, ux, vx):
    """the 8 forms (A, C, D) in (s, c) of sliceCons / sliceCons' (smax replaced by S)."""
    o, f, t, p, j = opt
    x, y = (vx, ux) if o == 1 else (ux, vx)
    fm = family(f, Nx, y)
    K, R, al, be, S, amin = fm['K'], fm['R'], fm['al'], fm['be'], fm['S'], fm['amin']
    L = x
    if t == 0:
        cs = [(-L, p * K, j * K - al), (L + 1, -p * K, al - 1 - j * K), (-R, K, -be), (R + 1, -K, be - 1),
              (1, 0, -2), (1, 0, -R), (-1, 0, S), (0, p, j - amin)]
    else:
        cs = [(-L, K, -al), (L + 1, -K, al - 1), (-R, p * K, j * K - be), (R + 1, -p * K, be - 1 - j * K),
              (1, 0, -2), (1, 0, -R), (-1, 0, S), (0, 1, -amin)]
    return cs, dict(K=K, L=L, R=R, S=S, x=x, y=y, **{k: fm[k] for k in ('al', 'be', 'amin', 'smax')})


def pf_forms(opt, Nx, ux, vx):
    """the 13 forms (A, C, D) in (a, c) of famConsC (famCons cleared by its positive denominators,
    smax replaced by S); opt = (o, f)."""
    o, f = opt[:2]
    x, y = (vx, ux) if o == 1 else (ux, vx)
    fm = family(f, Nx, y)
    K, R, al, be, S, amin = fm['K'], fm['R'], fm['al'], fm['be'], fm['S'], fm['amin']
    L = x
    al, be = sp.Integer(al), sp.Integer(be)
    cs = [(K, 0, -al * (L + 1) - (1 - al) * L - L * (L + 1)),
          (K * (R + 1), -K * L, -al * (R + 1) - (1 - be) * L - L * (R + 1)),
          (K, 0, -al - (R + 1) * L), (K, 0, -al - 3 * L),
          (-K * R, K * (L + 1), -be * (L + 1) - (1 - al) * R - R * (L + 1)),
          (0, K, -be * (R + 1) - (1 - be) * R - R * (R + 1)),
          (0, K, -be - (R + 1) * R), (0, K, -be - 3 * R),
          (-K, 0, (S - 1) * (L + 1) - (1 - al)), (0, -K, (S - 1) * (R + 1) - (1 - be)),
          (0, 0, S - R - 1), (0, 0, S - 3), (1, 0, -amin)]
    return cs, dict(K=K, L=L, R=R, S=S, x=x, y=y, **{k: fm[k] for k in ('al', 'be', 'amin', 'smax')})


ID = (1, 0, 0, 1)


X = sp.symbols('X0 X1 X2')


def conditions(opt, Nx, ux, vx, c0, i0, i1, dirn=ID, kind='slice'):
    """the conditions as affine functions of the corner variables X0, X1, X2 and their definitions.
    side (1, 0) of a slice [dirn = ID]: X = (c0, s0, s1), the 15 hypotheses of sliceH (in order);
    otherwise X = (Pa, Pc, delta) and the 4 |cs| corner conditions (form-major, corners
    P, P + w1, P + w2 + delta w1, P + w1 + w2 + delta w1).  c0 is the bottom line nu0 (coordinate
    along w2), i0, i1 the active lower forms in t."""
    cs, P = (slice_forms if kind == 'slice' else pf_forms)(opt, Nx, ux, vx)
    if dirn == ID and kind == 'slice':
        def low(i, c):
            A, C, D = cs[i]
            return -(C * c + D) / A
        defs = [sp.together(c0), sp.together(low(i0, c0)), sp.together(low(i1, c0 + 1))]
        C0, S0, S1 = X
        ev = lambda i, s_, c: cs[i][0] * s_ + cs[i][1] * c + cs[i][2]  # noqa: E731
        conds = []
        for i, up in ((0, True), (1, False), (2, True), (3, False), (4, False), (5, False), (6, True)):
            conds.append(ev(i, S0 + (1 if up else 0), C0))
            conds.append(ev(i, S1 + (1 if up else 0), C0 + 1))
        conds.append(ev(7, 0, C0))
        return conds, defs, P
    p1, q1, p2, q2 = dirn
    tf = [(A * p1 + C * q1, A * p2 + C * q2, D) for A, C, D in cs]

    def low(i, nu):
        A, C, D = tf[i]
        return -(C * nu + D) / A
    t0 = sp.together(low(i0, c0))
    t1 = sp.together(low(i1, c0 + 1))
    defs = [sp.together(c0 * p2 + t0 * p1), sp.together(c0 * q2 + t0 * q1), sp.together(t1 - t0)]
    Pa, Pc, dl = X
    corners = [(Pa, Pc), (Pa + p1, Pc + q1), (Pa + p2 + dl * p1, Pc + q2 + dl * q1),
               (Pa + p1 + p2 + dl * p1, Pc + q1 + q2 + dl * q1)]
    conds = []
    for A, C, D in cs:
        for a, c in corners:
            conds.append(A * a + C * c + D)
    return conds, defs, P


def split_def(e, sample):
    """e = num / den, den > 0 at the sample."""
    n, d = sp.fraction(sp.together(sp.expand(e)))
    n, d = sp.expand(n), sp.expand(d)
    if d.subs(sample) < 0:
        n, d = -n, -d
    return n, d


def pull_linear(n, sample):
    """n = prod(pulled linear factors, positive at the sample) * Q; returns (pulled, Q)."""
    n = sp.expand(n)
    if n.is_number:
        return [], n
    cst, fl = sp.factor_list(n)
    pulled, rest = [], sp.Integer(1)
    for fac, mult in fl:
        fac = sp.expand(fac)
        if sp.Poly(fac).total_degree() == 1 and fac.subs(sample) != 0:
            if fac.subs(sample) < 0:
                fac = -fac
                cst *= (-1) ** mult
            pulled += [fac] * mult
        else:
            rest *= fac ** mult
    return pulled, sp.expand(cst * rest)


def clear_cond(E, defs, vars_, sample):
    """E affine in X, defs X_i = n_i / d_i.  Returns (P, d, coefs, nd) with E d - P =
    sum_i coefs_i (X_i d_i - n_i) identically, d > 0 at the sample, P polynomial in vars."""
    nd = [split_def(e, sample) for e in defs]
    A = [sp.expand(sp.diff(E, x)) for x in X]
    A0 = sp.expand(E - sum(a * x for a, x in zip(A, X)))
    Et = sp.together(A0 + sum(a * n / d for a, (n, d) in zip(A, nd)))
    n, d = sp.fraction(Et)
    n, d = sp.expand(n), sp.expand(d)
    if d.subs(sample) < 0:
        n, d = -n, -d
    for _ in range(4):
        changed = False
        for a, (ni, di) in zip(A, nd):
            if a == 0:
                continue
            q = sp.cancel(a * d / di)
            qd = sp.fraction(q)[1]
            if qd != 1:
                d = sp.expand(d * qd)
                changed = True
        if not changed:
            break
    coefs = [sp.expand(sp.cancel(a * d / di)) for a, (ni, di) in zip(A, nd)]
    P = sp.expand(sp.cancel(Et * d))
    chk = sp.expand(E * d - P - sum(c * (x * di - ni) for c, x, (ni, di) in zip(coefs, X, nd)))
    assert chk == 0, chk
    return P, d, coefs, nd


def cleared(E, vars_, sample):
    """E = P / D with D > 0 (D: product of the denominators); returns (P, D)."""
    E = sp.together(sp.expand(E))
    n, d = sp.fraction(E)
    n, d = sp.expand(n), sp.expand(d)
    if d.subs(sample) < 0:
        n, d = -n, -d
    return n, d


# ---------------------------------------------------------------- pieces

class Piece:
    def __init__(self, name, vars_, Nx, ux, vx, hyps, opt, c0, act, doc='', target=None, dirn=ID, kind='slice'):
        self.dirn, self.kind = dirn, kind
        self.name, self.vars, self.Nx, self.ux, self.vx = name, list(vars_), Nx, ux, vx
        self.hyps = [clear_int(h) for h in hyps]
        self.opt, self.c0, self.act, self.doc = opt, sp.nsimplify(c0), act, doc
        self.target = target

    def forms(self):
        return self.hyps + [v for v in self.vars]

    def sample(self):
        # a point inside the domain (for the sign of denominators): solve roughly
        from scipy.optimize import linprog
        import numpy as np
        A, b = [], []
        for h in self.hyps:
            p = sp.Poly(h, *self.vars)
            row = [-float(p.coeff_monomial(v)) for v in self.vars]
            A.append(row)
            b.append(float(p.coeff_monomial(1)) - 1e-3)
        r = linprog([1.0] * len(self.vars), A_ub=A, b_ub=b, bounds=[(0, None)] * len(self.vars), method='highs')
        return {v: sp.Rational(round(x * 1000) + 1000, 1000) for v, x in zip(self.vars, r.x)}

    def certify(self, maxdeg=4, verbose=False):
        conds, defs, P = conditions(self.opt, self.Nx, self.ux, self.vx, self.c0, *self.act, dirn=self.dirn, kind=self.kind)
        smp = self.sample()
        out = []
        ok = True
        for k, E in enumerate(conds):
            n, d, coefs, nd = clear_cond(E, defs, self.vars, smp)
            pulled, Q = pull_linear(n, smp)
            r = handelman(Q, self.forms(), self.vars, maxdeg)
            if r is None:
                ok = False
                if verbose:
                    print('  FAIL', self.name, k, sp.factor(n), '/', sp.factor(d))
            out.append((E, n, d, r, coefs, pulled, Q))
        return ok, out, defs, [split_def(e, smp) for e in defs], P

    # ------------------------------------------------------------ Lean
    def lean(self, res):
        ok, out, defs, nds, P = res
        assert ok
        V = self.vars
        o, f = self.opt[:2]
        smp = self.sample()
        L = []
        if self.doc:
            L.append('/-- %s -/' % self.doc)
        hyps = ' '.join('(h%d : %s)' % (i, nat_ineq(h, V)) for i, h in enumerate(self.hyps))
        Ns, us, vs = (lean_nat(e, V) for e in (self.Nx, self.ux, self.vx))
        par = lambda s_: s_ if all(ch.isalnum() for ch in s_) else '(%s)' % s_  # noqa: E731
        reg = 'RegionSL' if self.kind == 'slice' else 'RegionPF'
        concl = self.target or '%s %s %s %s' % (reg, par(Ns), par(us), par(vs))
        L.append('theorem %s {%s : ℕ} %s :\n    %s := by' % (self.name, ' '.join(map(str, V)), hyps, concl))
        for i, fm in enumerate(self.forms()):
            if i < len(self.hyps):
                L.append('  have f%d : (0 : ℚ) ≤ %s := by' % (i, lean_poly(fm, V)))
                L.append('    have h := (Nat.cast_le (α := ℚ)).mpr h%d; push_cast at h; linarith' % i)
            else:
                L.append('  have f%d : (0 : ℚ) ≤ %s := by positivity' % (i, lean_poly(fm, V)))
        _, Pm = (slice_forms if self.kind == 'slice' else pf_forms)(self.opt, self.Nx, self.ux, self.vx)
        dens = {}

        def norm_fac(fac):
            fac = sp.expand(fac)
            return (-fac, -1) if fac.subs(smp) < 0 else (fac, 1)

        def factors(d):
            """d = cst * prod(factors) with the factors normalised; returns (cst, [indices])."""
            cst, fl = sp.factor_list(sp.expand(d))
            idx = []
            for fac, mult in fl:
                if sp.expand(fac).is_number:
                    cst *= fac ** mult
                    continue
                nf, sg = norm_fac(fac)
                cst *= sg ** mult
                if nf not in dens:
                    dens[nf] = len(dens)
                idx += [dens[nf]] * mult
            assert cst > 0, d
            return sp.nsimplify(cst), idx
        fd = [factors(d) for E, n, d, r, c, pl, Q in out]
        for E, n, d, r, c, pl, Q in out:
            for fac in pl:
                if fac not in dens:
                    dens[fac] = len(dens)
        fdef = [factors(d) for n, d in nds]
        for fac, k in list(dens.items()):
            L.append('  have hd%d : (0 : ℚ) < %s := by linarith' % (k, lean_poly(fac, V)))
        facl = list(dens)

        def cstr(c):
            return str(c) if c.is_Integer else '(%s : ℚ)' % c

        def prod_str(cst, idx):
            if not idx:
                return cstr(cst), '(by norm_num)'
            pf = 'hd%d' % idx[0]
            for k in idx[1:]:
                pf = 'mul_pos (%s) hd%d' % (pf, k)
            prod = ' * '.join('(%s)' % lean_poly(facl[k], V) for k in idx)
            if cst != 1:
                pf = 'mul_pos (by norm_num : (0 : ℚ) < %s) (%s)' % (cstr(cst), pf)
                prod = '%s * (%s)' % (cstr(cst), prod)
            return prod, '(%s)' % pf
        for i, ((n, d), (cst, idx)) in enumerate(zip(nds, fdef)):
            ds, dp = prod_str(cst, idx)
            L.append('  obtain ⟨x%d, hx%d⟩ : ∃ x : ℚ, x * (%s) = %s :=' % (i, i, ds, lean_poly(n, V)))
            L.append('    ⟨(%s) / (%s), div_mul_cancel₀ _ (ne_of_gt %s)⟩' % (lean_poly(n, V), ds, dp))
        Nl = par(Ns)
        smax = Pm['smax'] % Nl
        S = Pm['S']
        L.append('  have hS : %s ≤ ((%s : ℕ) : ℚ) := by' % (lean_rat(S, V), smax))
        L.append('    have h : %s ≤ 2 * (%s)%s := by omega' % (
            Nl + (' + 1' if f == 0 else ''), smax, ' + 1' if f == 2 else ''))
        L.append("    have h' := (Nat.cast_le (α := ℚ)).mpr h; push_cast at h'; linarith")
        idx = (f if o == 1 else 3 + f)
        x, y = (vs, us) if o == 1 else (us, vs)
        Kq, Lq, Rq = (lean_rat(Pm[k], V) for k in ('K', 'L', 'R'))
        hR = '(by push_cast; ring)' if f == 0 else \
            '(by rw [Nat.cast_sub (show 2 ≤ %s by omega)]; push_cast; ring)' % y
        head = '(Kq := %s) (Lq := %s) (Rq := %s) (S := %s)' % (Kq, Lq, Rq, lean_rat(S, V))
        if self.kind == 'slice' and self.dirn == ID:
            t = self.opt[2]
            cert = ('%s %s (c0 := x0) (s0 := x1) (s1 := x2)\n      (by push_cast; ring) (by push_cast; ring) %s hS %s' %
                    ('sliceH' if t == 0 else "sliceH'", head, hR, ' '.join(['?_'] * 15)))
        else:
            p1, q1, p2, q2 = self.dirn
            if self.kind == 'pf':
                cert = ('pfC %s (Pa := x0) (Pc := x1) (δ := x2)\n      (p1 := %d) (q1 := %d) (p2 := %d) (q2 := %d)\n'
                        '      (by push_cast; ring) (by push_cast; ring) %s hS (by linarith) (by linarith) (by norm_num) ?_' %
                        (head, p1, q1, p2, q2, hR))
            else:
                cert = ('%s %s (Pa := x0) (Pc := x1) (δ := x2)\n      (p1 := %d) (q1 := %d) (p2 := %d) (q2 := %d)\n'
                        '      (by push_cast; ring) (by push_cast; ring) %s hS (by norm_num) ?_' %
                        ('sliceG' if self.opt[2] == 0 else "sliceG'", head, p1, q1, p2, q2, hR))
        if self.kind == 'slice':
            t, p, j = self.opt[2:]
            inner = '⟨%d, %d, %s (%s)⟩' % (p, j, 'Or.inl' if t == 0 else 'Or.inr', cert)
        else:
            inner = '(%s)' % cert
        if idx in (1, 2, 4, 5):
            inner = '⟨by omega, %s⟩' % inner
        wrap = ('Or.inl %s' % inner) if idx < 5 else inner
        for k in range(idx):
            wrap = 'Or.inr (%s)' % wrap
        L.append('  refine %s' % wrap)
        if not (self.kind == 'slice' and self.dirn == ID):
            lst = {'pf': 'famConsC', 'slice': 'sliceQ' if self.opt[2] == 0 else "sliceQ'"}[self.kind]
            L.append("  simp only [Corners, %s, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp," % lst)
            L.append("    forall_eq, Aff.eval]")
            L.append("  refine ⟨%s⟩" % ', '.join(['⟨?_, ?_, ?_, ?_⟩'] * (13 if self.kind == 'pf' else 8)))
        for (E, n, d, r, coefs, pl, Q), (cst, idx2) in zip(out, fd):
            deg, supp = r
            hs = []
            for comb in supp:
                if len(comb) >= 2:
                    tt = 'f%d' % comb[0]
                    for ii in comb[1:]:
                        tt = 'mul_nonneg (%s) f%d' % (tt, ii)
                    hs.append(tt)
            dl, dpos = prod_str(cst, idx2)
            lc = ' + '.join('(%s) * hx%d' % (lean_poly(c, V), i) for i, c in enumerate(coefs) if c != 0) or '0'
            L.append('  · push_cast')
            if pl:
                pf = 'le_of_lt hd%d' % dens[pl[0]]
                for fac in pl[1:]:
                    pf = 'mul_nonneg (%s) (le_of_lt hd%d)' % (pf, dens[fac])
                hp = '(by have hq : (0 : ℚ) ≤ %s := (by linarith [%s]); have := mul_nonneg (%s) hq; linarith)' % (
                    lean_poly(Q, V), ', '.join(hs), pf)
            else:
                hp = '(by linarith [%s])' % ', '.join(hs)
            L.append('    exact nonneg_of_cleared (D := %s) (P := %s) %s %s' %
                     (dl, lean_poly(n, V), dpos, hp))
            L.append('      (by linear_combination %s)' % lc)
        return '\n'.join(L) + '\n'
