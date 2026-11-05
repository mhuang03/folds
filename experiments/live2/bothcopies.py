"""bothcopies.py N1 N2: splits [N] = X + Y with both X and Y window copies (|X| <= |Y|)."""
import sys
from lib import load_copies
from showchains import beatty_tag

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    cs = set(frozenset(X) for X, _ in load_copies(N))
    full = frozenset(range(1, N + 1))
    for X in sorted(cs, key=lambda s: (len(s), sorted(s))):
        Y = full - X
        if Y in cs and len(X) <= len(Y) and (len(X) < len(Y) or min(X) < min(Y)):
            print(N, sorted(X), beatty_tag(N, sorted(X)), '|', sorted(Y), beatty_tag(N, sorted(Y)))
