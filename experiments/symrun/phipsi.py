# phi(K) = G(K, K - floor(K/2)),  psi(K) = G(K, K - ceil(K/2))  (the two diagonal states)
# computed by the recursion  phi(2m) = phi(m), phi(2m+1) = max(phi(m), phi(m+1)),
#                             psi(2m) = phi(m), psi(2m+1) = max(psi(m), psi(m+1))   (K >= 28)
# from the DFS base (K <= 36); prints the level sets on [18M, 36M] for M = 2^j.
import subprocess
from functools import lru_cache

Gt = {}
out = subprocess.run(['./symrun.bin', 'base'], capture_output=True, text=True).stdout
for line in out.splitlines():
    if line.startswith('K='):
        k, rest = line.split(':')
        K = int(k[2:])
        for a, g in enumerate(map(int, rest.split()), 1):
            Gt[(K, K - a)] = g


@lru_cache(None)
def phi(K):
    if K <= 36:
        return Gt[(K, K // 2)]
    m = K // 2
    return phi(m) if K % 2 == 0 else max(phi(m), phi(m + 1))


@lru_cache(None)
def psi(K):
    if K <= 36:
        return Gt[(K, (K + 1) // 2)]
    m = K // 2
    return phi(m) if K % 2 == 0 else max(psi(m), psi(m + 1))


def runs(f, lo, hi):
    out, start = [], lo
    for K in range(lo + 1, hi + 2):
        if K > hi or f(K) != f(start):
            out.append((start, K - 1, f(start)))
            start = K
    return out


for j in range(0, 7):
    M = 2 ** j
    print('M =', M)
    print('  phi:', [(a - 18 * M, b - 18 * M, v) for a, b, v in runs(phi, 18 * M, 36 * M)])
    print('  psi:', [(a - 18 * M, b - 18 * M, v) for a, b, v in runs(psi, 18 * M, 36 * M)])
