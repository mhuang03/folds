"""xcopy.py: X_N = {1, 4, 6, ..., N-3, N} (N = 3 mod 4): copy check and co-reachability."""
import sys
from lib import imb, solve
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 4):
    X = [1] + list(range(4, N - 2, 2)) + [N]
    copy = all(imb(N, set(X) - {x}, x) == 0 for x in X)
    comp = [x for x in range(1, N + 1) if x not in X]
    o = solve(N, X, comp, key=lambda x: abs(2 * x - N - 1))
    print(N, len(X), 'copy' if copy else 'NOT copy', 'coreach' if o else 'NOT coreach', o, flush=True)
