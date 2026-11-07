# forced.py q nu : with the root choice fixed to 0 (reversal symmetry), which node choices are
# forced in parity-tree GoodL(q, nu) orders.  Prints per level k the nodes a (0-indexed residue
# a mod 2^k): 0/1 forced, '*' free.
import sys
from ptree import solve, nodes
q, nu = int(sys.argv[1]), int(sys.argv[2])
base = {(0, 0): 0}
print('exists', bool(solve(q, nu, fixed=base)))
nd = nodes(q)
lev = {}
for (k, a) in nd:
    if (k, a) == (0, 0):
        continue
    r = []
    for b in (0, 1):
        f = dict(base); f[(k, a)] = b
        r.append(bool(solve(q, nu, fixed=f)))
    c = '*' if all(r) else ('0' if r[0] else ('1' if r[1] else '-'))
    lev.setdefault(k, []).append((a, c))
for k in sorted(lev):
    print(k, ' '.join(f'{a}:{c}' for a, c in lev[k]))
