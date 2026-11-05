"""Numerical value of the rigorous lower bound  a(N) >= |F_s(N)| =: B(N)  (slip family).

  log B(1) = 0;  log B(2m+1) = log B(m) + log B(m+1);
  log B(2n)  = 2 log B(n) + log C(G(n), s(2n)),
       G(n) = |C_n| - 6 s(n)   (|C_n| = n/2 for n even, floor((n+1)/4) for n odd; s(odd) = 0)
  with the slip counts s(2n) = floor(n / K)  (needs s(2n) <= G(n)).
Also the power-of-two version with s(2^l) = floor(delta 2^(l-1)).
"""
import math, sys

def lgC(a, b):
    if b < 0 or b > a:
        return float('-inf')
    return math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)

def Cn(n):
    return n // 2 if n % 2 == 0 else (n + 1) // 4

def table(Nmax, K):
    f = [0.0] * (Nmax + 1); s = [0] * (Nmax + 1)
    for N in range(2, Nmax + 1):
        if N % 2:
            f[N] = f[N // 2] + f[N // 2 + 1]
        else:
            n = N // 2
            s[N] = n // K
            G = Cn(n) - 6 * s[n]
            assert s[N] <= G, (N, s[N], G)
            f[N] = 2 * f[n] + lgC(G, s[N])
    return f

def pow2(L, delta):
    f = 0.0; s_prev = 0
    for l in range(1, L + 1):
        n = 2 ** (l - 1)
        s = int(delta * n) if n >= 2 else 0
        G = Cn(n) - 6 * s_prev if n >= 2 else 0
        if s > G:
            return None
        f = 2 * f + lgC(G, s)
        s_prev = s
    return f

if __name__ == '__main__':
    # power of two: best delta
    best = None
    for i in range(1, 126):
        d = i / 1000
        v = pow2(30, d)
        if v is not None and (best is None or v > best[1]):
            best = (d, v)
    d = best[0]
    print(f"powers of two: best delta = {d}")
    for L in (10, 15, 20, 25, 30, 40):
        N = 2 ** L; v = pow2(L, d)
        print(f"  N=2^{L}: log B = {v:.6g},  log B/(N ln N) = {v / (N * math.log(N)):.4f},"
              f"  (log B - 0.1162 N ln N)/N = {(v - 0.1162 * N * math.log(N)) / N:.3f}")
    for K in (16, 13):
        f = table(1 << 20, K)
        print(f"all N, s(2n) = floor(n/{K}):")
        for N in (100, 1000, 10000, 100000, 1 << 20, (1 << 20) - 1, 3 * (1 << 18) + 1):
            print(f"  N={N}: log B = {f[N]:.6g}, log B/(N ln N) = {f[N] / (N * math.log(N)):.4f}")
        # worst ratio (log B - N ln N /48)/N over N
        worst = min((f[N] - N * math.log(N) / 48) / N for N in range(2, 1 << 20))
        print(f"  min_N (log B - N ln N/48)/N = {worst:.4f}")
