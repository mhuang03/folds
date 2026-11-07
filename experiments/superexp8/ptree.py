"""ptree.py: parity-tree class orders, the binary form of the X-condition, and a SAT solver.

0-indexed classes u = s - 1 in [0, q).  A parity tree is a choice g[(k, a)] in {0, 1} for every
node (k, a) (the classes u = a mod 2^k with at least two members): the subclass with bit k
equal to g comes first.  eps(k, u) = g[(k, u mod 2^k)] XOR bit_k(u) = 1 iff the sibling class
{t : v2(t - u) = k} is placed before u.

Binary form of Lemma X (PROOFS.txt 2.1): pi = tree order is GoodL(q, nu) iff for every u
   sum over j in [1, nu] with 2s - j outside [1, q] of  eps(v2(s - j - w_j q), s) - eps(v2(s - j), s) = 0
(w_j = +1 if 2s - j > q, -1 if 2s - j < 1), eps(inf) = 0.
"""
import sys
sys.path.insert(0, '../hyph')
from lib import goodL, valid, sig


def v2(x):
    if x == 0:
        return None
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


def nodes(q):
    """all nodes (k, a) with >= 2 members."""
    res = []
    k = 0
    while (1 << k) < q:
        for a in range(1 << k):
            cnt = len(range(a, q, 1 << k))
            if cnt >= 2:
                res.append((k, a))
        k += 1
    return res


def order(q, g):
    """the parity-tree order (1-indexed classes)."""
    def rec(k, a):
        mem = list(range(a, q, 1 << k))
        if len(mem) == 1:
            return [a + 1]
        f = g.get((k, a), 0)
        first = a + (f << k)
        second = a + ((1 - f) << k)
        return rec(k + 1, first) + rec(k + 1, second)
    return rec(0, 0)


def eps_var(q, k, u):
    """(node, bit): eps = g[node] XOR bit."""
    return (k, u % (1 << k)), (u >> k) & 1


def constraints(q, nu):
    """for each s: list of (sign, k) terms."""
    res = {}
    for s in range(1, q + 1):
        terms = []
        for j in range(1, nu + 1):
            x = 2 * s - j
            if 1 <= x <= q:
                continue
            w = 1 if x > q else -1
            ka = v2(s - j - w * q)
            kb = v2(s - j)
            if ka is not None:
                terms.append((+1, ka))
            if kb is not None:
                terms.append((-1, kb))
        # cancel
        cnt = {}
        for sg, k in terms:
            cnt[k] = cnt.get(k, 0) + sg
        res[s] = {k: c for k, c in cnt.items() if c != 0}
    return res


def binary_ok(q, nu, g):
    C = constraints(q, nu)
    for s, d in C.items():
        u = s - 1
        tot = 0
        for k, c in d.items():
            node, bit = eps_var(q, k, u)
            tot += c * (g.get(node, 0) ^ bit)
        if tot != 0:
            return False
    return True


def solve(q, nu, fixed=None, allsol=False, limit=None):
    from pysat.solvers import Solver
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    pool = IDPool()
    var = {nd: pool.id(nd) for nd in nodes(q)}
    clauses = []
    C = constraints(q, nu)
    for s, d in C.items():
        u = s - 1
        pos, neg = [], []
        for k, c in d.items():
            node, bit = eps_var(q, k, u)
            if node not in var:  # singleton node: its class is not split (cannot happen for real terms)
                raise Exception('bad node')
            lit = var[node] if bit == 0 else -var[node]   # lit true <=> eps = 1
            (pos if c > 0 else neg).extend([lit] * abs(c))
        if not pos and not neg:
            continue
        # sum pos - sum neg = 0  <=>  sum pos + sum(not neg) = len(neg)
        lits = pos + [-l for l in neg]
        # duplicates: handle by expanding with fresh copies
        uniq = []
        for l in lits:
            if l in uniq or -l in uniq:
                y = pool.id(('copy', len(clauses), len(uniq)))
                clauses.append([-y, l]); clauses.append([y, -l])
                uniq.append(y)
            else:
                uniq.append(l)
        enc = CardEnc.equals(lits=uniq, bound=len(neg), vpool=pool, encoding=EncType.seqcounter)
        clauses.extend(enc.clauses)
    if fixed:
        for nd, b in fixed.items():
            if nd in var:
                clauses.append([var[nd] if b else -var[nd]])
    sols = []
    with Solver(name='cadical153', bootstrap_with=clauses) as S:
        while S.solve():
            m = set(x for x in S.get_model() if x > 0)
            g = {nd: (1 if v in m else 0) for nd, v in var.items()}
            sols.append(g)
            if not allsol or (limit and len(sols) >= limit):
                break
            S.add_clause([-v if v in m else v for v in var.values()])
    return sols


if __name__ == '__main__':
    import random
    # check the binary form against GoodL on random trees
    bad = 0
    for q in range(2, 40):
        nd = nodes(q)
        for nu in range(q):
            for _ in range(30):
                g = {x: random.randint(0, 1) for x in nd}
                pi = order(q, g)
                assert valid(q, pi)
                if goodL(q, nu, pi) != binary_ok(q, nu, g):
                    bad += 1
    print('mismatches', bad)
    # solver agrees with goodL
    for q in range(2, 34):
        row = ''
        for nu in range(q):
            s = solve(q, nu)
            if s:
                assert goodL(q, nu, order(q, s[0]))
            row += 'Y' if s else '.'
        print(q, row)
