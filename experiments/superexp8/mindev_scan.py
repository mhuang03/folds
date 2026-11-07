# mindev_scan.py lo hi numax: for each q in [lo, hi], nu <= numax: the fewest deviations from the
# van der Corput tree (all choices 0) among parity-tree GoodL(q, nu) orders, and the deepest
# level of a deviating node.  Output: q nu ndev maxlevel  (or 'none').
import sys
from mindev import mindev
lo, hi, numax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
for q in range(lo, hi + 1):
    out = []
    for nu in range(0, min(numax, q - 1) + 1):
        g = mindev(q, nu, 0)
        if g is None:
            out.append(f'{nu}:none')
            continue
        dev = [nd for nd in g if g[nd]]
        ml = max((k for k, a in dev), default=-1)
        out.append(f'{nu}:{len(dev)}/{ml}')
    print(q, ' '.join(out), flush=True)
