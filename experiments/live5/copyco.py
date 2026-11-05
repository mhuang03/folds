"""copyco.py N u v pmin: copies containing u, v (copydfs) of size >= pmin: co-reachability of the
copy (exact) and of the preimage pair (exact), and whether the copy is inward."""
import subprocess
import sys
from lib import solve, coreach
from zeroset import inward_set

N, u, v, pmin = map(int, sys.argv[1:5])
out = subprocess.run(['./copydfs', str(N), str(u), str(v)], capture_output=True, text=True).stdout
for line in out.splitlines():
    head, X = line.split(':')
    p = int(head.split()[0][2:])
    if p < pmin or p == N:
        continue
    X = [int(x) for x in X.split()]
    pu, pv = X.index(u) + 1, X.index(v) + 1
    comp = [x for x in range(1, N + 1) if x not in X]
    cX = 'inward' if inward_set(N, set(X)) else ('coreach' if len(comp) <= 26 and solve(N, X, comp) else 'no')
    cp = coreach(p, [pu, pv]) if p <= 28 else '?'
    print(p, (pu, pv), cX, cp, X, flush=True)
