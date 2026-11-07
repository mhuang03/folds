# mindev.py q nu [default]: parity-tree GoodL(q, nu) order with the fewest nodes deviating from
# the default choice (default 0 = lower subclass first everywhere = van der Corput order).
# Prints the deviating nodes (k, a) with the members of node a mod 2^k (0-indexed).
import sys
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF, IDPool
from pysat.card import CardEnc, EncType
from ptree import nodes, constraints, eps_var, order
sys.path.insert(0, '../hyph')
from lib import goodL


def build(q, nu, pool):
    var = {nd: pool.id(nd) for nd in nodes(q)}
    cls = []
    for s, d in constraints(q, nu).items():
        u = s - 1
        pos, neg = [], []
        for k, c in d.items():
            node, bit = eps_var(q, k, u)
            lit = var[node] if bit == 0 else -var[node]
            (pos if c > 0 else neg).extend([lit] * abs(c))
        if not pos and not neg:
            continue
        lits = pos + [-l for l in neg]
        uniq = []
        for l in lits:
            if l in uniq or -l in uniq:
                y = pool.id(('copy', s, len(uniq)))
                cls.append([-y, l]); cls.append([y, -l])
                uniq.append(y)
            else:
                uniq.append(l)
        cls.extend(CardEnc.equals(lits=uniq, bound=len(neg), vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    return var, cls


def mindev(q, nu, default=0):
    pool = IDPool()
    var, cls = build(q, nu, pool)
    w = WCNF()
    for c in cls:
        w.append(c)
    for nd, v in var.items():
        w.append([-v] if default == 0 else [v], weight=1)
    with RC2(w) as r:
        m = r.compute()
        if m is None:
            return None
        ms = set(x for x in m if x > 0)
        return {nd: (1 if v in ms else 0) for nd, v in var.items()}


if __name__ == '__main__':
    q, nu = int(sys.argv[1]), int(sys.argv[2])
    df = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    g = mindev(q, nu, df)
    if g is None:
        print('none'); sys.exit()
    assert goodL(q, nu, order(q, g))
    dev = sorted(nd for nd in g if g[nd] != df)
    print(q, nu, 'deviations', len(dev))
    for k, a in dev:
        print('  ', (k, a), list(range(a, q, 1 << k))[:6], '...' if len(range(a, q, 1 << k)) > 6 else '')
