"""verify_w.py -- check the identity  w1(F_{S,T}) = w2(F_{S,T}) = 0  for ALL pairs (S,T) of windows
of Theta(M) (S a reversed tail, T a head), where F_{S,T}(g,h) = Pi^{(g,h)}_M(S,T) and
    w1(F) = F(-1,0) - F(-1,1) - F(0,0) + F(0,1),   w2(F) = F(0,-1) - F(0,0) - F(1,-1) + F(1,0).
(Delta = w1 + w2 is the amplitude of the 1/4-mode.)  W_M is the exact window set for M <= 18
and, for M >= 19, the set of windows of positive weight produced by Theorem J.
Usage: python3 verify_w.py M1 M2 ...   (one line per M: #pairs, #pairs with w1 != 0, w2 != 0)"""
import sys
import numpy as np
import wl
from delta import pi_gh

W1 = np.zeros(9, dtype=np.int64); W2 = np.zeros(9, dtype=np.int64)
st = {(g, h): 3 * (g + 1) + (h + 1) for g in (-1, 0, 1) for h in (-1, 0, 1)}
for s, c in (((-1, 0), 1), ((-1, 1), -1), ((0, 0), -1), ((0, 1), 1)):
    W1[st[s]] = c
for s, c in (((0, -1), 1), ((0, 0), -1), ((1, -1), -1), ((1, 0), 1)):
    W2[st[s]] = c

if __name__ == "__main__":
    for M in [int(a) for a in sys.argv[1:]]:
        L = wl.law(M)
        w = L.win
        n1 = n2 = 0
        for s0 in range(0, len(w), 256):
            P = pi_gh(M, w[s0:s0 + 256], w).astype(np.int64)
            n1 += int(((P @ W1) != 0).sum()); n2 += int(((P @ W2) != 0).sum())
        print(f"M={M} M%3={M % 3} |W|={len(w)} pairs={len(w) ** 2} w1!=0: {n1} w2!=0: {n2}", flush=True)
