"""pieces.py: the thin-line pieces (diagonal v = u + d, strip v = 2u + e, ...) and their designs.
python3 pieces.py NAME...   -- fit c0 and certify the named pieces (see PIECES)
"""
import sys
import os
import pickle
import sympy as sp
from gen import Piece, save_cache
from design2 import best_fit

N, u = sp.symbols('N u')


def opt_of(code):
    a, j = code.split(':')
    return (int(a[0]), int(a[1]), int(a[2]), int(a[3]), int(j))


# diagonal lines: d -> (option, umin of the main piece)
DIAG = {0: ('1001:0', 6), 2: ('1001:1', 4), 3: ('1201:2', 6), 4: ('0111:1', 4), 5: ('1011:-2', 4),
        6: ('0101:-2', 6), 7: ('0101:-2', 4), 8: ('1011:-3', 8), 9: ('0111:3', 5)}


def diag_piece(d, umin, code=None, extra=(), tag=''):
    code = code or DIAG[d][0]
    hyps = [N - 301, u - umin, N - 3 * u - 2 * d - 1] + list(extra)
    nm = 'diag%d%s' % (d, tag)
    return Piece(nm, [N, u], N, u, u + d, hyps, opt_of(code), 0, None,
                 doc='The line `u\' = u + %d`, slice %s.' % (d, code))


def d1_corner():
    return Piece('d1_corner', [N, u], N, u, u + 1, [N - 301, u - 5, N - 3 * u - 4, 3 * u + 20 - N],
                 opt_of('1101:1'), 0, None, dirn=(3, 1, -1, 0),
                 doc="The corner of the line `u' = u + 1`: `3u + 4 ≤ N ≤ 3u + 20`, slice X0 `a = c + 1`, side `(3, 1)`.")


def shape(us, vs, code, nmin=301):
    return Piece('shape_%d_%d' % (us, vs), [N], N, sp.Integer(us), sp.Integer(vs), [N - nmin], opt_of(code), 0, None,
                 doc="The shape `(%d, %d)`, slice %s." % (us, vs, code))


# fixed shapes on the diagonal lines (u below the main pieces)
SHAPES = [(4, 4, '1110:1'), (4, 5, '1110:1'), (4, 7, '1001:1'), (5, 8, '1001:1'), (4, 10, '1003:-1'),
          (5, 11, '1002:0'), (4, 12, '1002:1'), (5, 13, '1002:1'), (6, 14, '1002:1'), (7, 15, '1002:0'),
          (4, 13, '1003:0')]

# strip lines v = 2u + e: e -> (option, umin)
STRIP = {-12: ('0012:-6', 4), -11: ('0212:-6', 4), -10: ('0212:-5', 4), -9: ('0212:-5', 4), -8: ('0212:-5', 4),
         -7: ('1002:-3', 4), -6: ('1002:-3', 4), -5: ('1202:-1', 4), -4: ('1202:0', 4), -3: ('1202:0', 4),
         -2: ('0112:-2', 4), -1: ('0212:-2', 4), 0: ('0012:0', 4), 1: ('1202:2', 4), 2: ('1002:1', 4),
         3: ('1002:1', 4), 4: ('0112:1', 4), 5: ('0112:1', 4), 6: ('1102:4', 7), 7: ('0112:2', 4),
         8: ('1002:3', 4), 9: ('0112:3', 5), 10: ('0112:3', 4), 11: ('0112:4', 6), 12: ('0112:4', 5),
         13: ('0112:5', 8), 14: ('0112:5', 6), 15: ('1002:6', 8)}


w = sp.Symbol('w')


def strip_shift(e):
    """u = w + a, v = 2w + b with a, b >= 0 (no truncated subtraction in Lean)."""
    a = max(0, (-e + 1) // 2)
    return a, 2 * a + e


def strip_piece(e, umin=None, code=None, extra=(), tag=''):
    code = code or STRIP[e][0]
    umin = umin or STRIP[e][1]
    a, b = strip_shift(e)
    U, Vv = w + a, 2 * w + b
    hyps = [N - 301, U - umin, U + e - 10, 8 * U + 320 - N, N - 5 * U - 2 * e - 1] + list(extra)
    nm = 'strip%s%s' % (('m%d' % -e) if e < 0 else str(e), tag)
    return Piece(nm, [N, w], N, U, Vv, hyps, opt_of(code), 0, None,
                 doc="The line `u' = 2u %s %d` of the strip (`u = w + %d`), slice %s." % ('-' if e < 0 else '+', abs(e), a, code))


SSHAPES = [(6, 4), (6, 5), (6, 6), (9, 4), (11, 4), (11, 5), (12, 4), (13, 4), (13, 5), (13, 6), (13, 7),
           (14, 4), (14, 5), (15, 4), (15, 5), (15, 6), (15, 7)]


def sshape(e, us, code='0000:2'):
    return Piece('sshape_%d_%d' % (us, 2 * us + e), [N], N, sp.Integer(us), sp.Integer(2 * us + e),
                 [N - 301, 8 * us + 320 - N], opt_of(code), 0, None,
                 doc="The shape `(%d, %d)` of the strip (`N ≤ %d`), slice %s." % (us, 2 * us + e, 8 * us + 320, code))


PIECES = {}
for e, us in SSHAPES:
    PIECES['sshape_%d_%d' % (us, 2 * us + e)] = (lambda e=e, us=us: sshape(e, us))
PIECES['shape_3_9'] = lambda: shape(3, 9, '1002:1')
PIECES['shape_3_10'] = lambda: shape(3, 10, '1002:1')
for e in STRIP:
    PIECES['strip%d' % e] = (lambda e=e: strip_piece(e))
for d, (code, umin) in DIAG.items():
    PIECES['diag%d' % d] = (lambda d=d, umin=umin: diag_piece(d, umin))
PIECES['d1corner'] = d1_corner
for us, vs, code in SHAPES:
    PIECES['shape_%d_%d' % (us, vs)] = (lambda us=us, vs=vs, code=code: shape(us, vs, code))


DESIGNS = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tmp',
                       os.environ.get('DESIGNS_FILE', 'designs.pkl'))


def load_designs(path=DESIGNS):
    try:
        return pickle.load(open(path, 'rb'))
    except Exception:
        return {}


def all_designs():
    import glob
    d = {}
    for fn in sorted(glob.glob(os.path.join(os.path.dirname(DESIGNS), 'designs*.pkl'))):
        d.update(load_designs(fn))
    return d


def save_design(key, val):
    d = load_designs()
    d[key] = val
    os.makedirs(os.path.dirname(DESIGNS), exist_ok=True)
    pickle.dump(d, open(DESIGNS, 'wb'))


def run_tree(key, mk, splitter, tag='', extra=()):
    """certify the piece mk(extra, tag); on failure split along splitter(tag) (two closed halves).
    Returns the tree: Piece (leaf), (form, tree_ge, tree_le), or None (failure)."""
    pc = mk(extra, tag)
    res = run(pc, verbose=False)
    if res is not None:
        save_design((key, tag), (tuple(extra), res.c0, res.act))
        return res
    f = splitter(tag)
    if f is None:
        print('  UNSPLITTABLE FAIL', pc.name, flush=True)
        return None
    return (f, run_tree(key, mk, splitter, tag + 'a', tuple(extra) + (f,)),
            run_tree(key, mk, splitter, tag + 'b', tuple(extra) + (-f,)))


def run(pc, verbose=True):
    r = best_fit(pc, pc.opt, verbose=False)
    if r is None:
        print(pc.name, 'NO FIT')
        return None
    c0, act, slack = r
    pc.c0, pc.act = c0, act
    ok, out, s0, s1, P = pc.certify(verbose=verbose)
    print(pc.name, 'c0 =', c0, 'act', act, 'slack %.3f' % slack, 'CERT' if ok else 'FAIL', flush=True)
    save_cache()
    return pc if ok else None


def strip_tree(e):
    a, b = strip_shift(e)
    U = w + a
    sp_ = {'': 2 * N - 13 * U, 'a': 4 * N - 29 * U, 'b': 4 * N - 23 * U,
           'aa': 8 * N - 61 * U, 'ab': 8 * N - 55 * U, 'ba': 8 * N - 49 * U, 'bb': 8 * N - 43 * U}
    return run_tree(('strip', e), lambda extra, tag: strip_piece(e, extra=extra, tag=tag), lambda t: sp_.get(t))


def diag_tree(d):
    code, umin = DIAG[d]
    sp_ = {'': 40 - u, 'a': 14 - u, 'b': 200 - u}
    return run_tree(('diag', d), lambda extra, tag: diag_piece(d, umin, extra=extra, tag=tag), lambda t: sp_.get(t))


if __name__ == '__main__':
    for nm in sys.argv[1:]:
        if nm.startswith('stree'):
            print(nm, strip_tree(int(nm[5:])), flush=True)
        elif nm.startswith('dtree'):
            print(nm, diag_tree(int(nm[5:])), flush=True)
        else:
            r = run(PIECES[nm]())
            if r is not None:
                save_design((nm, ''), ((), r.c0, r.act))
