# Region invariance for the halving recursion of G (PROOFS.txt, Theorem F).
# (K, a) -> (ceil(K/2), #odd values in [K-a+1, K]) and (floor(K/2), #even values there).
# Checks: 2a <= K + c  implies  2a' <= K' + c for c = 2, 3 (all K <= KMAX, all a),
# and that the f-relevant pairs (both parities, both extreme u) satisfy 2a <= K + 1.
import sys
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4000

def images(K, a):
    lo = K - a + 1
    ao = (K + 1) // 2 - lo // 2
    ae = K // 2 - (lo - 1) // 2
    return [((K + 1) // 2, ao), (K // 2, ae)]

for c in (1, 2, 3):
    bad = []
    for K in range(2, KMAX + 1):
        for a in range(0, K + 1):
            if 2 * a > K + c: break
            for K2, a2 in images(K, a):
                if 2 * a2 > K2 + c: bad.append((K, a, K2, a2))
    print(f"c={c}: violations of invariance for K<={KMAX}:", len(bad), bad[:6])

def linked(N, y, u):
    z1, z2 = 2 * y - u, 2 * u - y
    return 1 <= z1 <= N or 1 <= z2 <= N

worst = -99
for N in range(3, 3000):
    for p in (0, 1):
        KD = (N + 1) // 2 if p else N // 2
        for u in range(1, N + 1):
            if u % 2 == p: continue
            a = sum(1 for y in range(2 - p, N + 1, 2) if not linked(N, y, u))
            worst = max(worst, 2 * a - KD)
print("max over N<3000 of 2|A(u)| - |D|:", worst)
