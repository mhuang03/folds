"""Sanity checks of the engine on sequences with known recurrences."""
import random
from common import *

random.seed(1)
rows = [[random.randint(1, 100) for _ in range(5)] for _ in range(8)]
r = analyze(rows)
print('random 8x5      ', fmt(r))
assert r['rank'] == 5 and r['excess'] == 0

f = [factorial(n) for n in range(40)]
rows = [[f[n], n * f[n - 1], f[n - 1]] for n in range(2, 38)]
r = analyze(rows, [0])
print('n! = n*(n-1)!   ', fmt(r), r['kernel'])
assert r['genuine']

# Motzkin numbers: (n+2) M_n = (2n+1) M_{n-1} + 3(n-1) M_{n-2}
M = [1, 1]
for n in range(2, 38):
    M.append(((2 * n + 1) * M[-1] + 3 * (n - 1) * M[-2]) // (n + 2))
rows = [[n ** j * M[n - i] for i in range(3) for j in range(3)] for n in range(2, 38)]
r = analyze(rows, [0, 1, 2])
print('Motzkin r=2 d=2 ', fmt(r))
assert r['genuine']
# near-miss detection: sequence that follows Motzkin up to n=20 and then deviates
M2 = M[:21] + [x + 1 for x in M[21:]]
rows = [[n ** j * M2[n - i] for i in range(3) for j in range(3)] for n in range(2, 38)]
r = analyze(rows, [0, 1, 2])
print('Motzkin broken  ', fmt(r))
assert r['excess'] > 5 and not r['kernel']
print('ok')
