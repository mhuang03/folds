# enumerate the base states (X', Y') (K' in [18,36]) reached at level M = 2^j by
# N in [36M, 72M) (j <= 3, which covers every class by Lemma 4); print them with G values
import subprocess

Gt = {}
out = subprocess.run(['./symrun.bin', 'base'], capture_output=True, text=True).stdout
for line in out.splitlines():
    if line.startswith('K='):
        k, rest = line.split(':')
        K = int(k[2:])
        for a, g in enumerate(map(int, rest.split()), 1):
            Gt[(K, K - a)] = g


def pairs(N):
    K, L = N // 2, (N + 1) // 4
    M = 1
    while 72 * M <= N:
        M *= 2
    return M, {((K + c) // M, (L + c) // M) for c in range(M)}


S = {}
for N in range(36, 577):
    M, P = pairs(N)
    for s in P:
        S.setdefault(s, []).append(N)
for s in sorted(S):
    print(s, 'G=', Gt.get(s), 'a=', s[0] - s[1], 'N e.g.', S[s][:4])
print(len(S), 'states')
