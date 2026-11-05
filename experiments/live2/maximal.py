"""maximal.py N1 N2: maximal window copies of [N] (not contained in a larger copy).
A copy X inside a copy V is automatically a copy of V's strip, so complements compose:
[N] \\ X is reachable if [N] \\ V is and V \\ X is reachable in V's strip."""
import sys
from lib import load_copies
from showchains import beatty_tag

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    cs = [(frozenset(X), g) for X, g in load_copies(N)]
    for X, good in cs:
        if not any(X < V for V, _ in cs):
            print(N, len(X), sorted(X), beatty_tag(N, sorted(X)), 'good' if good else 'BAD')
