"""chaintbl.py Q: the table chainTbl of Folds/Live2.lean: for 2 <= q <= Q, nu < q, s in 1..q, an
order of the classes other than s satisfying ChainOK q nu (empty for exceptional s, which
have none by RS).  Printed as a Lean list literal."""
import sys
from chainok import find


def exc(q, nu, s):
    return q & (q - 1) != 0 and ((nu == 1 and s == 1) or (nu + 1 == q and s == q))


Q = int(sys.argv[1])
tbl = [[], []]
for q in range(2, Q + 1):
    rows = []
    for nu in range(q):
        row = []
        for s in range(1, q + 1):
            r = [] if exc(q, nu, s) else find(q, nu, s)
            assert r is not None, (q, nu, s)
            row.append(r)
        rows.append(row)
    tbl.append(rows)
    print(q, file=sys.stderr)
print(repr(tbl).replace(' ', ''))
