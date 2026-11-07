"""special.py -- the window pairs carrying the 1/4-mode (w1 != 0) at a size M with 3 ! M: list the
rows (reversed tails) and columns (heads) involved and their first entries."""
import sys
import numpy as np
import wl
from delta import pi_gh
from verify_w import W1, W2

M = int(sys.argv[1])
L = wl.law(M)
P = pi_gh(M, L.win, L.win).astype(np.int64)
a = P @ W1; b = P @ W2
rows = np.nonzero((a != 0).any(axis=1))[0]; cols = np.nonzero((a != 0).any(axis=0))[0]
print("M", M, "rows", len(rows), "cols", len(cols), "product set:", (a != 0).sum() == len(rows) * len(cols))
print("first entries of rows (y'_1 = last entry of sigma):", sorted(set(L.win[rows, 0].tolist())))
print("first entries of cols (u_1 = first entry of tau):", sorted(set(L.win[cols, 0].tolist())))
print("w1 values:", sorted(set(a[a != 0].tolist())), " w2 values:", sorted(set(b[b != 0].tolist())))
for r in rows[:4]:
    for c in cols[:3]:
        print("  S=", L.win[r].tolist(), "T=", L.win[c].tolist(), "F=", P[r, c].reshape(3, 3).tolist(), "w1", a[r, c], "w2", b[r, c])
rows2 = np.nonzero((b != 0).any(axis=1))[0]; cols2 = np.nonzero((b != 0).any(axis=0))[0]
print("w2 rows first entries:", sorted(set(L.win[rows2, 0].tolist())), "cols:", sorted(set(L.win[cols2, 0].tolist())))
