"""automaton.py -- the shift automaton behind the fair-bit model.

LEMMA (unlifting).  Let L be even, y = 2Y - b, u = 2U - c (b, c in {0,1}).  Then
    1 + g <= 2y - u <= L + g   <=>   1 + g' <= 2Y - U <= L/2 + g',   g' = floor((g + 2b - c)/2),
and the same for 2u - y with h' = floor((h + 2c - b)/2).
So Pi_{N}(lifted windows) = Pi^{(g,h)}(unlifted windows) at size N/2, where Pi^{(g,h)} uses
"linked_{g,h}(L, y, u) :<=> 1+g <= 2y-u <= L+g  or  1+h <= 2u-y <= L+h".
Top level N (q = top bit, D-bits b = q, C-bits c = 1-q):  (0,0) -> (-1,1) or (1,-1).
Below: (b, c) are the top bits of the two windows; uniform in the fair-bit model.
State space {-1,0,1}^2.  This script prints the transition matrix and its spectrum.
"""
import itertools
import numpy as np
from fractions import Fraction

S = list(itertools.product([-1, 0, 1], repeat=2))
idx = {s: i for i, s in enumerate(S)}


def step(s, b, c):
    g, h = s
    return ((g + 2 * b - c) // 2, (h + 2 * c - b) // 2)


T = np.zeros((9, 9))
for s in S:
    for b in (0, 1):
        for c in (0, 1):
            T[idx[s], idx[step(s, b, c)]] += 0.25

if __name__ == "__main__":
    print("states", S)
    print("T (row = from):")
    for i, s in enumerate(S):
        print(s, " ".join(str(Fraction(x).limit_denominator(8)) for x in T[i]))
    ev, V = np.linalg.eig(T.T)
    print("eigenvalues:", np.round(sorted(ev.real, reverse=True), 6))
    # Jordan structure: rank of (T - lambda)^k
    for lam in (1, 0.5, 0.25, 0):
        A = T - lam * np.eye(9)
        print("lambda", lam, "ranks of (T-l)^k:", [np.linalg.matrix_rank(np.linalg.matrix_power(A, k), tol=1e-9) for k in (1, 2, 3)])
    p = np.zeros(9); p[idx[(-1, 1)]] = 0.5; p[idx[(1, -1)]] = 0.5
    print("distribution after the top step and k further steps:")
    for k in range(6):
        print(k, " ".join(str(Fraction(x).limit_denominator(10 ** 6)) for x in p))
        p = p @ T
