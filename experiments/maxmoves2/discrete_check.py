"""discrete_check.py -- V(S) for a discretised continuum configuration (clusters -> adjacent
panels).  V uses the definition of check2adic.c (m free and #S in [m-D, m) = #S in (m, m+D],
D = min(m-1, N-m)).  usage: python3 discrete_check.py"""
from fractions import Fraction as F


def V(N, S):
    Sset = set(S)
    pre = [0] * (N + 1)
    for m in range(1, N + 1):
        pre[m] = pre[m - 1] + (m in Sset)
    v = 0
    for m in range(1, N + 1):
        if m in Sset:
            continue
        D = min(m - 1, N - m)
        if pre[m - 1] - pre[m - 1 - D] == pre[m + D] - pre[m]:
            v += 1
    return v


def discretise(xs, N):
    S = []
    for x in sorted(xs):
        p = max(1, round(x * N))
        while p in S:
            p += 1
        S.append(p)
    return S


configs = {
    4: [F(3, 7), F(3, 7), F(5, 7), F(6, 7)],
    12: [F(3, 14)] * 3 + [F(17, 56), F(2, 5), F(3, 7), F(17, 28), F(17, 28), F(5, 7),
                         F(45, 56), F(6, 7), F(6, 7)],
}
for s, xs in configs.items():
    for N in (560, 2240, 8960, 35840):
        S = discretise(xs, N)
        v = V(N, S)
        print("s=%d N=%d V=%d V/N=%.5f  (5/7=%.5f, 23/32=%.5f, size bound %.5f)" %
              (s, N, v, v / N, 5 / 7, 23 / 32, (6 * N + 2 - 2 * s) / 8 / N))
