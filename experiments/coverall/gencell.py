"""gencell.py: Lean code for the bulk cells (key polynomials and ParOK from the keys).

A cell = (name, family, orientation, (p, q, p2, q2), edge).  Variables in Lean: N u v : ℕ
(v = u'), cast to ℚ.  Family Z: K = N + 2, (x, y) = (v, u) for orientation 1, alpha = 0,
beta = 1, amin = 2, smax = (N + 2)/2, s0 = (N + 1)/2.
The key conditions at sigma3 (edge4) / tau1 (edge1), for both variants 8, 9, cleared:
  P = A n + B den   with   sigma = n / den.
"""
import sympy as sp

Nn, uu, vv = sp.symbols('N u v')


def lean_poly(e):
    """sympy polynomial in N, u, v -> Lean ℚ expression string (expanded)."""
    e = sp.expand(e)
    p = sp.Poly(e, Nn, uu, vv)
    terms = []
    for mon, c in zip(p.monoms(), p.coeffs()):
        factors = []
        for var, k in zip(('N', 'u', 'v'), mon):
            if k == 1:
                factors.append(var)
            elif k > 1:
                factors.append('%s ^ %d' % (var, k))
        c = int(c)
        body = ' * '.join(factors)
        if not body:
            terms.append((c, None))
        else:
            terms.append((c, body))
    s = ''
    for i, (c, body) in enumerate(terms):
        if body is None:
            t = str(abs(c))
        elif abs(c) == 1:
            t = body
        else:
            t = '%d * %s' % (abs(c), body)
        if i == 0:
            s = ('-' if c < 0 else '') + t
        else:
            s += (' - ' if c < 0 else ' + ') + t
    return s


def fam(name, o):
    N, u, v = Nn, uu, vv
    x, y = (v, u) if o == 1 else (u, v)
    if name == 'Z':
        return dict(K=N + 2, L=x, R=y, al=0, be=1, amin=2, s0=(N + 1) / sp.Integer(2))
    if name == 'X0':
        return dict(K=N, L=x, R=y - 2, al=0, be=1, amin=1, s0=N / sp.Integer(2))
    if name == 'X1':
        return dict(K=N, L=x, R=y - 2, al=1, be=0, amin=2, s0=(N - 1) / sp.Integer(2))


def keys(fname, o, p, q, edge):
    f = fam(fname, o)
    K, L, R, al, be, amin, s0 = f['K'], f['L'], f['R'], f['al'], f['be'], f['amin'], f['s0']
    s = sp.Symbol('s')
    out = []
    if edge == 4:
        Dl = q * (L + 1) - p * R
        v8 = s0 - 1 - K * p / (L + 1)
        v9 = ((s0 - 1) * (R + 1) - K * q - 1) / R - 1
        conds = [('chord', (s * (L + 1) - 1 + K * p) * (R + 1) - ((s + 1) * R + 1 + K * q) * L - L * (R + 1)),
                 ('bot', s - (L + 1)), ('botR', s - (R + 1)),
                 ('amin', s * (L + 1) + al - 1 - amin * K)]
    else:
        Dl = p * (R + 1) - q * L
        v8 = ((s0 - 1) * (L + 1) - K * p - 1) / L - 1
        v9 = s0 - 1 - K * q / (R + 1)
        conds = [('chord', (s * (R + 1) - 1 + K * q) * (L + 1) - ((s + 1) * L + 1 + K * p) * R - R * (L + 1)),
                 ('bot', s - (L + 1)), ('botR', s - (R + 1)),
                 ('amin', (s + 1) * L + al - amin * K)]
    for vn, vexpr in (('8', v8), ('9', v9)):
        sig = sp.together(vexpr - K / Dl)
        n, den = sp.fraction(sig)
        # normalise den positive-looking: keep as is
        for cn, ce in conds:
            e = sp.expand(ce)
            A = e.coeff(s, 1)
            B = sp.expand(e - A * s)
            P = sp.expand(A * n + B * den)
            out.append((cn + vn, P, n, den, sig, ce))
    return out, Dl, v8, v9


if __name__ == "__main__":
    for cell in (('Z', 1, 1, 1, 4), ('Z', 1, 2, 1, 4), ('Z', 1, 2, 1, 1)):
        ks, Dl, v8, v9 = keys(*cell)
        print(cell, 'Delta', Dl)
        for nm, P, n, den, sig, ce in ks:
            print('  ', nm, 'den =', sp.factor(den), ' deg', sp.Poly(P, Nn, uu, vv).total_degree())
            print('      ', lean_poly(P))
