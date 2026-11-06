"""gaplp2.py -- the discrete gap LP (exactly the hypotheses of arith_two_adic, relaxed to reals)
for given s and N: maximise sum z_k subject to
   2 z_0 <= w_0,  2 z_s <= w_s + 1,  2 z_{s/2} <= w_s + w_0 + 2,
   2 z_k <= w_{2k mod s} + 1 (other k),  z_k + 1 <= w_k (k < s),  sum w = N,  z, w >= 0.
Prints max V / N as a function of x = s/N (compare (a+1)/(a+2) and the chain bound
((a+1) - (a-1) x)/(a+2) + O(1/N)).  usage: python3 gaplp2.py"""
import numpy as np
from scipy.optimize import linprog

def lp(s, N):
    n = 2 * (s + 1)           # z_0..z_s, w_0..w_s
    Z = lambda k: k
    W = lambda k: s + 1 + k
    A, b = [], []
    def row(d, rhs):
        r = np.zeros(n)
        for i, c in d: r[i] += c
        A.append(r); b.append(rhs)
    row([(Z(0), 2), (W(0), -1)], 0)
    row([(Z(s), 2), (W(s), -1)], 1)
    for k in range(1, s):
        if 2 * k == s:
            row([(Z(k), 2), (W(s), -1), (W(0), -1)], 2)
        else:
            row([(Z(k), 2), (W((2 * k) % s), -1)], 1)
    for k in range(s):
        row([(Z(k), 1), (W(k), -1)], -1)
    Aeq = np.zeros((1, n)); Aeq[0, s + 1:] = 1
    c = np.zeros(n); c[:s + 1] = -1
    r = linprog(c, A_ub=np.array(A), b_ub=b, A_eq=Aeq, b_eq=[N], bounds=[(0, None)] * n)
    return -r.fun

def v2(k):
    a = 0
    while k % 2 == 0: k //= 2; a += 1
    return a

if __name__ == "__main__":
    for s in (2, 6, 4, 12, 20, 8, 24, 16):
        a = v2(s)
        out = []
        for x in (0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3):
            N = round(s / x)
            V = lp(s, N)
            chain = ((a + 1) * N - (a - 1) * s) / (a + 2)
            out.append("x=%.2f: %.4f (chain %.4f)" % (s / N, V / N, chain / N))
        print("s=%d a=%d  " % (s, a) + "  ".join(out))
