"""clpieces.py: the cluster box N <= 4u + 80, 4u <= N + 40, delta = N - 1 - u - 2v in [0, 80]
(v >= u + 10), covered by famCons parallelogram certificates (RegionPF) on polyhedral regions in
(r, delta), r = 4u - N.  python3 clpieces.py NAME..."""
import sys
import sympy as sp
from gen import Piece, save_cache
from design2 import best_fit
from pieces import save_design

N, u, v = sp.symbols('N u v')
r = 4 * u - N
dl = N - 1 - u - 2 * v
BOX = [N - 301, 4 * u + 80 - N, N + 40 - 4 * u, dl, 80 - dl, v - u - 10, 2 * u - v - 13]
NSC = list(range(301, 345, 3)) + [361, 402, 455, 503, 611, 702, 851, 1000, 1001, 1002, 1003, 1004, 1502, 2001, 3001, 5002, 10003, 30001]

DIRS = {(1, 1): (1, 1, 0, 1), (2, 1): (2, 1, 1, 1), (3, 2): (3, 2, 1, 1), (2, 3): (2, 3, 1, 2),
        (1, 2): (1, 2, 0, 1), (3, 1): (3, 1, 2, 1), (4, 3): (4, 3, 1, 1), (5, 3): (5, 3, 3, 2)}

# name -> (o, f, dir, extra region constraints (>= 0))
AL = 50 * dl + 31 * r - 825          # >= 0 : region A
BL = -(10 * dl + 13 * r + 130)       # >= 0 : region B
CD = 2 * v - 3 * u                   # >= 0 : delta + r <= -1 (D), <= -1 : C


def reg(nmin):
    return {
        'clA': (0, 1, (1, 1), [AL, N - nmin]),
        'clB': (1, 1, (2, 1), [BL, N - nmin]),
        'clD': (1, 1, (3, 2), [-AL, -BL, CD, N - nmin]),
        'clC': (0, 1, (2, 3), [-AL, -BL, -CD - 1, N - nmin]),
    }


CL = {}
for nmin in (301, 400, 600, 1000):
    for k, val in reg(nmin).items():
        CL['%s%d' % (k, nmin)] = val


def cl_piece(nm, extra=(), tag=''):
    o, f, d, reg = CL[nm]
    return Piece(nm + tag, [N, u, v], N, u, v, BOX + list(reg) + list(extra), (o, f), 0, None,
                 doc='The cluster region %s: famCons of %s, orientation %s, side %s.' % (
                     nm, ['Z', 'X0', 'X1'][f], "(u', u)" if o == 1 else "(u, u')", d),
                 dirn=DIRS[d], kind='pf')


def run(pc, verbose=True):
    pc.feats = [N, r, dl]
    r_ = best_fit(pc, pc.opt, Ns=NSC, verbose=False)
    if r_ is None:
        print(pc.name, 'NO FIT', flush=True)
        return None
    c0, act, slack = r_
    pc.c0, pc.act = c0, act
    ok, out, s0, s1, P = pc.certify(verbose=True)
    print(pc.name, 'nu0 =', c0, 'act', act, 'slack %.3f' % slack, 'CERT' if ok else 'FAIL', flush=True)
    save_cache()
    return pc if ok else None


if __name__ == '__main__':
    for nm in sys.argv[1:]:
        pc = run(cl_piece(nm))
        if pc is not None:
            save_design(('cl', nm), ((), pc.c0, pc.act))
