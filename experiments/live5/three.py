"""three.py n1 n2: for even n, the w with {1, w, n} co-reachable in [n]."""
import sys
from lib import coreach
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
    print(n, [w for w in range(2, n) if coreach(n, [1, w, n])], flush=True)
