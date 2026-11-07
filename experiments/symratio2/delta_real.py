"""delta_real.py -- Delta(Pi^{.}_M(S,T)) over ALL pairs of windows of Theta(M) (S a reversed
tail, T a head; both range over W_M), for the given sizes M.  Also the fair-model amplitude
Delta(F_t) = E_{t x t} Delta.  Usage: python3 delta_real.py M1 M2 ..."""
import sys
import numpy as np
import wl
from delta import pi_gh, V

for M in [int(a) for a in sys.argv[1:]]:
    L = wl.law(M)
    w = L.win
    nz = 0; vals = set(); amp = 0.0; pos = 0
    for s0 in range(0, len(w), 256):
        P = pi_gh(M, w[s0:s0 + 256], w)
        dl = P.astype(np.int64) @ V.astype(np.int64)
        nz += (dl != 0).sum(); pos += (dl > 0).sum()
        vals |= set(np.unique(dl).tolist())
        amp += L.t[s0:s0 + 256] @ dl @ L.t
    print(f"M={M} (M mod 3 = {M % 3}) |W|={len(w)} pairs with Delta!=0: {nz}, Delta>0: {pos}, "
          f"min Delta {min(vals)}, amplitude Delta(F_t)={amp:.4e}", flush=True)
