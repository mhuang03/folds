"""leaves.py: the bulk leaves (polyhedra in (N, u, v), v = u') and the LP certificates of the
key polynomials on them.  Usage: python3 leaves.py [leafname ...]"""
import sys, time
import sympy as sp
from gencell import keys, Nn, uu, vv
from handel import certify, products, certify_exact

N, u, v = Nn, uu, vv
T = [u - 4, v - u - 10, N - 1 - u - 2 * v, N - 301, u, v]
CL = {'a': N - 4 * u - 81, 'b': 4 * u - N - 41, 'c': N - 1 - u - 2 * v - 81}

LEAVES = {
    'L1a': (T + [3 * u - 2 * v, CL['a']], 'A'),
    'L1b': (T + [3 * u - 2 * v, CL['b']], 'A'),
    'L1c': (T + [3 * u - 2 * v, CL['c']], 'A'),
    'L2a': (T + [2 * v - 3 * u, 2 * u - v - 13, CL['a']], 'B1'),
    'L2c': (T + [2 * v - 3 * u, 2 * u - v - 13, CL['c']], 'B1'),
    'L4': (T + [v - 2 * u + 12, 2 * u - v + 15, N - 8 * u - 321], 'D'),
    'L5': (T + [v - 2 * u - 16, 3 * u - v, 10 * u - N], 'B4'),
    'L6': (T + [v - 2 * u - 16, 3 * u - v, N - 10 * u], 'D'),
    'L7a': (T + [v - 3 * u, 36 * N - 100 * v], 'D'),
    'L7b': (T + [v - 3 * u, 100 * v - 36 * N, N - 10 * u], 'B'),
    'L7c': (T + [v - 3 * u, 100 * v - 36 * N, 10 * u - N], 'D'),
}
CELLS = {'A': ('Z', 1, 1, 1, 4), 'B4': ('Z', 1, 2, 1, 4), 'B1': ('Z', 1, 2, 1, 1)}


def cell_polys(name):
    ks, Dl, v8, v9 = keys(*CELLS[name])
    return [(nm, P) for nm, P, n, den, sig, ce in ks]


def regD_polys():
    """RegionD with (u - u%2) replaced by (u - 1) (sufficient)."""
    M = N + 2
    P1 = (u - 1) * M * (u + v + 1) - 2 * (u + 1) * (M * u + 2 * u * v + u)
    P2 = ((u - 1) * M - 2 * u + 2) * (v + 1) - 2 * u * (v * v + M)
    return [('D1', sp.expand(P1)), ('D2', sp.expand(P2)), ('D3', sp.expand(N - u - v))]


def regB_polys():
    """RegionB with c = u/2 replaced by (u - 1)/2 (sufficient), n = N + 2 - 2v."""
    M = N + 2
    n = M - 2 * v
    c = (u - 1) / sp.Integer(2)
    B1 = c * M - (u + 1) * (n - 1)
    B2 = c * M - u * (u + 1)
    B3 = c * M * (n + 2 * u) - u * ((2 * u + 1) * n - 2 * u) - u * (u + 1) * (2 * n + M - 1)
    B4 = c * v - 2 * (u + 1)
    return [('B1', sp.expand(2 * B1)), ('B2', sp.expand(2 * B2)), ('B3', sp.expand(2 * B3)),
            ('B4', sp.expand(2 * B4)), ('Bn', sp.expand(n - 3))]


def run(leaf, maxdeg=4, verbose=True):
    forms, cell = LEAVES[leaf]
    polys = regD_polys() if cell == 'D' else regB_polys() if cell == 'B' else cell_polys(cell)
    res = {}
    prods = {}
    prods2 = {}
    import os, pickle
    cpath = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tmp', 'lpcache.pkl')
    try:
        cache = pickle.load(open(cpath, 'rb'))
    except Exception:
        cache = {}
    for nm, P in polys:
        t = time.time()
        key = (leaf, nm, str(forms), str(P))
        if key in cache:
            res[nm] = cache[key]
            continue
        r = None
        if os.environ.get('FASTLP'):
            for fs in (forms[:-2], forms):
                for deg in range(1, maxdeg + 1):
                    s_ = certify(P, fs, (N, u, v), deg, scale=1 if fs is not forms else 1000)
                    if s_:
                        r = (0, [c for c, _ in s_])
                        break
                if r:
                    break
        if r is None:
            r = certify_exact(P, forms[:-2], (N, u, v), maxdeg, prods2)
        if r is None:
            r = certify_exact(P, forms, (N, u, v), maxdeg, prods)
        if r is None:
            # unverified fallback: union of float supports (Lean's linarith decides)
            sel = set()
            for fs in (forms[:-2], forms):
                for deg in (2, 3, 4):
                    for sc in (1, 30, 1000):
                        s_ = certify(P, fs, (N, u, v), deg, scale=sc)
                        if s_:
                            sel |= set(c for c, _ in s_)
            if sel:
                r = (0, sorted(sel))
        found = (r[0], [(c, 1.0) for c in r[1]]) if r else None
        res[nm] = found
        cache[key] = found
        os.makedirs(os.path.dirname(cpath), exist_ok=True)
        pickle.dump(cache, open(cpath, 'wb'))
        if verbose:
            print(leaf, cell, nm, 'deg %s supp %s  %.1fs' % (found[0] if found else None,
                  len(found[1]) if found else None, time.time() - t), flush=True)
    return res


if __name__ == "__main__":
    names = sys.argv[1:] or list(LEAVES)
    for lf in names:
        run(lf)
