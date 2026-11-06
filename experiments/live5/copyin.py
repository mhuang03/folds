"""copyin.py N u v: copies containing u, v (copydfs) that satisfy the inward criterion, with the
preimage pair and whether that pair is in the family cov5 (all rules)."""
import subprocess
import sys
sys.argv, args = sys.argv[:1], sys.argv[1:]
from zeroset import inward_set  # noqa: E402
import cov5  # noqa: E402
import covlean4 as C4  # noqa: E402

sys.setrecursionlimit(100000)
N, u, v = map(int, args[:3])
cov = cov5.make_cov5(C4.make_cov(True))
out = subprocess.run(['./copydfs', str(N), str(u), str(v)], capture_output=True, text=True).stdout
for line in out.splitlines():
    head, X = line.split(':')
    p = int(head.split()[0][2:])
    if p == N:
        continue
    X = [int(x) for x in X.split()]
    if not inward_set(N, set(X)):
        continue
    pu, pv = X.index(u) + 1, X.index(v) + 1
    print(p, (pu, pv), cov(p, pu, pv), X)
