"""Which intervals [b, c] are reachable from scratch in [N]?  Prints, per N and b, the c's."""
import sys
from lib import reachable

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    print('N =', N)
    for b in range(1, N + 1):
        cs = [c for c in range(b, N + 1) if reachable(N, range(b, c + 1))]
        print('  b=%2d:' % b, ' '.join(map(str, cs)))
