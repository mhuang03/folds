"""look.py N u v [mode]: print orderings (background picture) of [N] minus {u, v}."""
import sys
from lib import solve
N, u, v = map(int, sys.argv[1:4])
mode = sys.argv[4] if len(sys.argv) > 4 else 'mid'
keys = {
    'mid': lambda x: abs(2 * x - N - 1),
    'small': lambda x: x,
    'large': lambda x: -x,
    'out': lambda x: -abs(2 * x - N - 1),
    'nearpair': lambda x: min(abs(x - u), abs(x - v)),
    'farpair': lambda x: -min(abs(x - u), abs(x - v)),
}
tg = [x for x in range(1, N + 1) if x not in (u, v)]
print(N, (u, v), mode, solve(N, [u, v], tg, keys[mode]))
