"""fwd.py N mode D...: forward (from scratch) orderings of [N] minus D, preferring keys."""
import sys
from lib import solve
N = int(sys.argv[1])
mode = sys.argv[2]
D = [int(x) for x in sys.argv[3:]]
keys = {
    'mid': lambda x: abs(2 * x - N - 1),
    'small': lambda x: x,
    'large': lambda x: -x,
    'out': lambda x: -abs(2 * x - N - 1),
}
tg = [x for x in range(1, N + 1) if x not in D]
print(N, D, mode, solve(N, [], tg, keys[mode]))
