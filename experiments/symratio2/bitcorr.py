"""bitcorr.py -- eps(m) = P(a1 = a2) - 1/2 for the top two head bits of Theta(m), along chains."""
import sys
import numpy as np
import wl
from bits import bitstring

for m in [int(a) for a in sys.argv[1:]]:
    L = wl.law(m)
    b = bitstring(L.win, m, 2)
    t = L.t
    e = t[b[:, 0] == b[:, 1]].sum() - 0.5
    p1 = t[b[:, 0] == 1].sum() - 0.5
    print(m, f"eps={e: .4e}  P(a1=1)-1/2={p1: .3e}", flush=True)
