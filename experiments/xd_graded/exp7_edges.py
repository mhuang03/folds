"""Experiment 7: exact edge counts of Gamma_N (all subsets) and the trace of the commutator.

Checks against out/levels.txt (N <= 24):
  e_k(N) = #{(S, m) : |S| = k, m not in S, (S, m) valid}
         = sum_{m=1}^{N} sum_j C(r_m, j)^2 C(N-1-2 r_m, k-2j),       r_m = min(m-1, N-m)
  e(N)   = sum_k e_k = sum_m 2^(N-1-2 r_m) C(2 r_m, r_m)
         = N C(N, N/2)                       (N even)
         = (2N-1) C(N-1, (N-1)/2)            (N odd)
  trace C_k = e_k - e_{k-1}   (C_k = D U - U D on rank k), compared with the Boolean value
              (N - 2k) C(N, k).
Also prints the 'effective r_k' = trace C_k / C(N, k).
"""
from math import comb
from fractions import Fraction

rows = {}
N = None
for line in open('out/levels.txt'):
    if line.startswith('N='):
        N = int(line.split()[0][2:])
        rows[N] = []
    elif line.strip()[0].isdigit():
        rows[N].append([int(x) for x in line.split()])

ok1 = ok2 = True
for N in sorted(rows):
    e = [r[4] for r in rows[N]]
    rm = [min(m - 1, N - m) for m in range(1, N + 1)]
    pred = [sum(sum(comb(r, j) ** 2 * comb(N - 1 - 2 * r, k - 2 * j)
                    for j in range(0, k // 2 + 1) if j <= r)
                for r in rm) for k in range(N + 1)]
    ok1 &= (pred == e)
    tot = sum(2 ** (N - 1 - 2 * r) * comb(2 * r, r) for r in rm)
    closed = N * comb(N, N // 2) if N % 2 == 0 else (2 * N - 1) * comb(N - 1, (N - 1) // 2)
    ok2 &= (tot == sum(e) == closed)
    if N in (8, 12, 16, 20, 24):
        tr = [e[k] - (e[k - 1] if k else 0) for k in range(N + 1)]
        print(f"N={N}: effective r_k = trace(C_k)/C(N,k), k=0..N/2:",
              [round(float(Fraction(tr[k], comb(N, k))), 3) for k in range(N // 2 + 1)],
              " (Boolean lattice: N-2k)")
print("per-rank edge formula holds for all N <= 24:", ok1)
print("total edge formula holds for all N <= 24:", ok2)
