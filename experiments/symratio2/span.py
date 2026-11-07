"""span.py -- the linear span of the 9-vectors F_{S,T}(g,h) = Pi^{(g,h)}_M(S,T) over all window
pairs of W_M, its dimension, and its annihilator (exact, via sympy on the distinct vectors)."""
import sys
import numpy as np
import sympy as sp
import wl
from delta import pi_gh

for M in [int(a) for a in sys.argv[1:]]:
    L = wl.law(M)
    P = pi_gh(M, L.win, L.win).reshape(-1, 9)
    U = np.unique(P, axis=0)
    A = sp.Matrix(U.tolist())
    ann = A.nullspace()
    print(f"M={M}: {len(U)} distinct vectors, rank {A.rank()}; annihilator basis:")
    for v in ann:
        v = v / sp.gcd(list(v)) if any(v) else v
        print("   ", list(v))
