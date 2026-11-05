"""adjcopies.py N1 N2: adjacent pairs {r, r+1} contained in a window copy with reachable
complement (a good copy); prints, per r, one such copy of smallest size (or '-')."""
import sys
from lib import load_copies
from showchains import beatty_tag

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    cs = [X for X, good in load_copies(N) if good]
    out = []
    for r in range(1, N):
        best = None
        for X in cs:
            if r in X and r + 1 in X and (best is None or len(X) < len(best)):
                best = X
        out.append(f'{r}:{best}{beatty_tag(N, best) if best else ""}' if best else f'{r}:-')
    print(N, ' '.join(out))
