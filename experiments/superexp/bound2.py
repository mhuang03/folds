"""Numerical check of Theorem 3 (PROOFS.txt section 4): the lower bound obtained from the
three proven recursions (log2 units)
   (R1) f(2n+1) >= 1 + f(n) + f(n+1)                      [Lean semiCount_odd]
   (R2) f(4m)   >= m + 4 f(m)                             [Lean semiCount_four_mul]
   (R3) f(4m+2) >= floor((m+1)/2) + 2 f(m) + 2 f(m+1)     [Lean semiCount_four_mul_add_two]
   (R0) f(2n)   >= 1 + 2 f(n)                             [Lean semiCount_even]
starting from f(1) = 0, stays above  g(N) = N log2 N / 32 - N/4 + 1/12  for all N <= Nmax.
Also reports L(N)/(N log2 N), the effective exponent of the recursion bound."""
import math, sys

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 20
f = [0.0] * (Nmax + 1)
for N in range(2, Nmax + 1):
    if N % 2:
        n = N // 2
        f[N] = 1 + f[n] + f[n + 1]
    else:
        n = N // 2
        best = 1 + 2 * f[n]
        if N % 4 == 0:
            m = N // 4
            best = max(best, m + 4 * f[m])
        else:
            m = (N - 2) // 4
            best = max(best, (m + 1) // 2 + 2 * f[m] + 2 * f[m + 1])
        f[N] = best
g = lambda N: N * math.log2(N) / 32 - N / 4 + 1 / 12
worst = min(f[N] - g(N) for N in range(1, Nmax + 1))
print(f"min_N<= {Nmax} (L(N) - g(N)) = {worst:.4f}  (>= 0 confirms the induction numerically)")
for N in (100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, 4 ** 10, 2 ** 20 - 1, 3 * 2 ** 18 + 1):
    if N <= Nmax:
        print(f"  N={N}: log2 bound = {f[N]:.1f}, / (N log2 N) = {f[N] / (N * math.log2(N)):.4f}")
