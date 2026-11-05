"""Best rigorous (exponential) lower bound obtainable from the exact values a(1..33) and the
proven recursions:
  parity       a(N)   >= 2 a(floor(N/2)) a(ceil(N/2))
  composition  a(qn)  >= a(q) a(n)^q                       (PROOFS.txt 1.1)
  splits       a((2j+1)n) >= 2 a(jn) a((j+1)n)             (PROOFS.txt 1.2)
Prints min over windows [M, 2M) of log B(N) / N.
"""
import math

a = {}
for line in open('../semi_counts.txt'):
    if line.startswith('#'):
        continue
    n, v = line.split()[:2]
    a[int(n)] = math.log(int(v))

TOP = 1 << 14
B = [0.0] * (TOP + 1)
for N in range(1, TOP + 1):
    if N in a:
        B[N] = a[N]
        continue
    best = math.log(2) + B[N // 2] + B[(N + 1) // 2]
    for q in range(2, int(N ** 0.5) + 1):
        if N % q == 0:
            n = N // q
            best = max(best, B[q] + q * B[n], B[n] + n * B[q])
    for j in range(1, 40):
        q = 2 * j + 1
        if q > N:
            break
        if N % q == 0:
            n = N // q
            best = max(best, math.log(2) + B[j * n] + B[(j + 1) * n])
    B[N] = best

M = 17
while 2 * M <= TOP:
    lo = min(range(M, 2 * M), key=lambda n: B[n] / n)
    print(f"N in [{M},{2*M}): min log B(N)/N = {B[lo]/lo:.4f} at N={lo};"
          f"  max = {max(B[n]/n for n in range(M, 2*M)):.4f}")
    M *= 2
