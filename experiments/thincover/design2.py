"""design2.py: c0 design for a generic Piece (gen.py): enumerate integer points of the piece's
domain on a sample (N <= 30002), compute the exact c0-windows (side (1, 0)) restricted to the
active lower bounds (i0, i1), and fit c0 linear in the piece variables (LP, max slack), rounded to a
small common denominator."""
from fractions import Fraction as F
import numpy as np
import sympy as sp
from scipy.optimize import linprog
from slicelib import window
from design import actwin

NS = (list(range(301, 420)) + list(range(420, 1200, 7)) + list(range(1200, 4000, 41)) +
      [5001, 5002, 10001, 10002, 30001, 30002])


def forms_exact(opt, N, u, v):
    """slice forms with smax replaced by the Lean lower bound S (as in gen.slice_forms)."""
    o, f, t, p, j = opt
    x, y = (v, u) if o == 1 else (u, v)
    if f == 0:
        K, R, al, be, S, amin = N + 2, y, 0, 1, F(N + 1, 2), 2
    elif f == 1:
        K, R, al, be, S, amin = N, y - 2, 0, 1, F(N, 2), 1
    else:
        K, R, al, be, S, amin = N, y - 2, 1, 0, F(N - 1, 2), 2
    L = x
    if t == 0:
        return [(-L, p * K, j * K - al), (L + 1, -p * K, al - 1 - j * K), (-R, K, -be), (R + 1, -K, be - 1),
                (1, 0, -2), (1, 0, -R), (-1, 0, S), (0, p, j - amin)]
    return [(-L, K, -al), (L + 1, -K, al - 1), (-R, p * K, j * K - be), (R + 1, -p * K, be - 1 - j * K),
            (1, 0, -2), (1, 0, -R), (-1, 0, S), (0, 1, -amin)]


def pf_exact(opt, N, u, v):
    """famCons forms (smax replaced by the Lean lower bound S), Fractions; opt = (o, f)."""
    o, f = opt[:2]
    x, y = (v, u) if o == 1 else (u, v)
    if f == 0:
        K, R, al, be, S, amin = N + 2, y, 0, 1, F(N + 1, 2), 2
    elif f == 1:
        K, R, al, be, S, amin = N, y - 2, 0, 1, F(N, 2), 1
    else:
        K, R, al, be, S, amin = N, y - 2, 1, 0, F(N - 1, 2), 2
    L = x
    U = [(F(K, L), F(0), F(-al, L)), (F(0), F(K, R), F(-be, R)), (F(0), F(0), S)]
    Lw = [(F(K, L + 1), F(0), F(1 - al, L + 1)), (F(0), F(K, R + 1), F(1 - be, R + 1)), (F(0), F(0), F(R)),
          (F(0), F(0), F(2))]
    cs = [(a[0] - b[0], a[1] - b[1], a[2] - b[2] - 1) for a in U for b in Lw]
    cs.append((F(1), F(0), F(-amin)))
    return cs


def points(pc, Ns=NS, umax=None):
    """integer assignments of the piece variables in the domain (sampled)."""
    V = [str(v) for v in pc.vars]
    hy = [sp.lambdify(pc.vars, h) for h in pc.hyps]
    fx = [sp.lambdify(pc.vars, e) for e in (pc.Nx, pc.ux, pc.vx)]
    out = []
    if len(V) == 2 and V[0] == 'N':
        for N in Ns:
            us = [u for u in range(0, N // 2 + 1) if all(h(N, u) >= 0 for h in hy)]
            if not us:
                continue
            st = max(1, len(us) // 60)
            sel = set(us[:60]) | set(us[::st]) | set(us[-40:])
            out += [(N, u) for u in sorted(sel)]
    elif V == ['N', 'u', 'v']:
        for N in Ns:
            for uu in range(max(0, (N - 80) // 4), (N + 40) // 4 + 1):
                for vv in range((N - 82 - uu) // 2, (N - uu) // 2 + 1):
                    if all(h(N, uu, vv) >= 0 for h in hy):
                        out.append((N, uu, vv))
    elif V == ['N']:
        out = [(N,) for N in Ns if all(h(N) >= 0 for h in hy)]
    elif len(V) == 1 and V[0] != 'N':
        us = list(range(0, 400)) + list(range(400, 2000, 7)) + list(range(2000, 12000, 97))
        out = [(u,) for u in us if all(h(u) >= 0 for h in hy)]
    else:
        raise ValueError(V)
    return [(pt, tuple(int(f(*pt)) for f in fx)) for pt in out]


def tforms(opt, N, u, v, dirn, kind='slice'):
    cs = (forms_exact if kind == 'slice' else pf_exact)(opt, N, u, v)
    if dirn is None or dirn == (1, 0, 0, 1):
        return cs
    p1, q1, p2, q2 = dirn
    return [(A * p1 + C * q1, A * p2 + C * q2, D) for A, C, D in cs]


def fit(pc, opt, act, Ns=NS, verbose=False, pts=None, wins=None):
    data, bad = [], []
    dirn = getattr(pc, 'dirn', None)
    if wins is None:
        pts = pts if pts is not None else points(pc, Ns)
        wins = [(pt, tforms(opt, N, u, v, dirn, getattr(pc, 'kind', 'slice'))) for pt, (N, u, v) in pts]
        wins = [(pt, cs, window(cs)) for pt, cs in wins]
    for pt, cs, w in wins:
        if w is not None and w[0] <= w[1]:
            w = actwin(cs, w, *act)
        if w is None or w[0] > w[1]:
            bad.append(pt)
        else:
            data.append((pt, w))
    if bad:
        return ('bad', bad[:8], len(bad))
    if not data:
        return ('empty',)
    feats = getattr(pc, 'feats', None) or list(pc.vars)
    ff = [sp.lambdify(pc.vars, e) for e in feats]
    data = [(tuple(F(f(*pt)) if not isinstance(f(*pt), F) else f(*pt) for f in ff), w) for pt, w in data]
    X = np.array([[1.0] + [float(x) for x in pt] for pt, w in data])
    lo = np.array([float(w[0]) for pt, w in data]); hi = np.array([float(w[1]) for pt, w in data])
    n = X.shape[1]
    A = np.vstack([np.hstack([-X, np.ones((len(X), 1))]), np.hstack([X, np.ones((len(X), 1))])])
    b = np.concatenate([-lo, hi])
    r = linprog([0] * n + [-1], A_ub=A, b_ub=b, bounds=[(None, None)] * (n + 1), method='highs')
    if r.status != 0:
        return ('lp',)
    c, t = r.x[:n], r.x[n]
    import itertools
    cands = []
    for k in range(1, n):
        rng = max(1.0, float(np.max(np.abs(X[:, k]))))
        tol = max(0.0005, min(0.02, 2.0 / rng))
        fr = sorted({F(round(c[k] * q), q) for q in range(1, 241)}, key=lambda x: (x.denominator, abs(float(x) - c[k])))
        fr = [x for x in fr if abs(float(x) - c[k]) <= tol][:10]
        if F(0) not in fr and abs(c[k]) < 0.01:
            fr = [F(0)] + fr
        cands.append(fr)
    scored = []
    for sl in itertools.product(*cands):
        sv = X[:, 1:] @ np.array([float(x) for x in sl]) if n > 1 else np.zeros(len(X))
        lo_, hi_ = np.max(lo - sv), np.min(hi - sv)
        if lo_ <= hi_:
            scored.append(((hi_ - lo_) / 2, max([x.denominator for x in sl] + [1]), sl))
    scored.sort(key=lambda z: -z[0])
    if scored:
        top = scored[0][0]
        good = [z for z in scored if z[0] >= top / 2]
        good.sort(key=lambda z: (z[1], -z[0]))
        for sk, _, sl in good[:6] + scored[:3]:
            lo_ = max(w[0] - sum(ci * xi for ci, xi in zip(sl, pt)) for pt, w in data)
            hi_ = min(w[1] - sum(ci * xi for ci, xi in zip(sl, pt)) for pt, w in data)
            if lo_ > hi_:
                continue
            mid = (lo_ + hi_) / 2
            for q in range(1, 241):
                a0 = F(round(mid * q), q)
                if lo_ <= a0 <= hi_:
                    break
            expr = sp.Rational(a0.numerator, a0.denominator) + sum(
                sp.Rational(ci.numerator, ci.denominator) * v for ci, v in zip(sl, feats))
            return ('ok', sp.expand(expr), float((hi_ - lo_) / 2))
    return ('round', c, t)


def best_fit(pc, opt, Ns=NS, combos=None, verbose=False):
    best = None
    pts = points(pc, Ns)
    if not pts:
        return None
    dirn = getattr(pc, 'dirn', None)
    wins = [(pt, tforms(opt, N, u, v, dirn, getattr(pc, 'kind', 'slice'))) for pt, (N, u, v) in pts]
    wins = [(pt, cs, window(cs)) for pt, cs in wins]
    if combos is None and getattr(pc, 'kind', 'slice') == 'pf':
        # the most frequent active lower forms at the window centres
        from collections import Counter
        from slicelib import maxlow
        cnt = Counter()
        for pt, cs, w in wins:
            if w is None or w[0] > w[1]:
                continue
            c = (w[0] + w[1]) / 2
            cnt[(maxlow(cs, c)[1], maxlow(cs, c + 1)[1])] += 1
        combos = [k for k, _ in cnt.most_common(3)]
    if combos is None:
        pt, cs, w = wins[len(wins) // 2]
        lows = [i for i, (A, C, D) in enumerate(cs) if A > 0]
        combos = [(a, b) for a in lows for b in lows]
    for act in combos:
        r = fit(pc, opt, act, Ns, wins=wins)
        if verbose:
            print('   ', act, r)
        if r[0] == 'ok' and (best is None or r[2] > best[2]):
            best = (r[1], act, r[2])
    return best
