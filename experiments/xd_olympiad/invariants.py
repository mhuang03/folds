"""Attempts 4 and 5: conserved quantities and candidate involutions, by enumeration (N <= 11).
 (a) rank of the affine span of the time vectors (t_1..t_N) over Q (mod a big prime) and over
     F_2, F_3: every missing dimension is a linear invariant sum c_m t_m = const (mod p).
 (b) K(x,y) = #valid a such that exchanging the TIMES of panels x and y keeps a valid
     (a sign-reversing partial involution);  best pairs.
 (c) R(k) = #valid a such that exchanging STEPS k, k+1 keeps a valid (= consecutive pair commutes).
 (d) two-chain data: #distinct left orders sigma, #distinct (sigma, rho), max #shuffles."""
import sys
from common import *

def rank_mod(vecs, p):
    rows = []
    piv = []
    for v in vecs:
        v = [x % p for x in v]
        for r, c in zip(rows, piv):
            if v[c]:
                f = v[c]
                v = [(a - f * b) % p for a, b in zip(v, r)]
        nz = next((i for i, x in enumerate(v) if x), None)
        if nz is not None:
            inv = pow(v[nz], p - 2, p)
            v = [(x * inv) % p for x in v]
            rows.append(v); piv.append(nz)
    return len(rows)

def main(Nmax):
    for N in range(3, Nmax + 1):
        L, R = masks(N)
        seqs = list(valid_seqs(N))
        V = set(seqs)
        t0 = None; diffs = {2: [], 3: [], 1000003: []}
        basis_cap = N + 2
        ranks = {}
        tv = []
        for a in seqs:
            t = [0] * N
            for i, m in enumerate(a): t[m - 1] = i + 1
            tv.append(t)
        t0 = tv[0]
        for p in (2, 3, 1000003):
            # incremental elimination
            rows = []; piv = []
            for t in tv:
                v = [(x - y) % p for x, y in zip(t, t0)]
                for r, c in zip(rows, piv):
                    if v[c]:
                        f = v[c]; v = [(a - f * b) % p for a, b in zip(v, r)]
                nz = next((i for i, x in enumerate(v) if x), None)
                if nz is not None:
                    iv = pow(v[nz], p - 2, p); v = [(x * iv) % p for x in v]
                    rows.append(v); piv.append(nz)
            ranks[p] = len(rows)
        # (b)
        K = {}
        for x in range(1, N + 1):
            for y in range(x + 1, N + 1):
                c = 0
                for a in seqs:
                    b = tuple(y if m == x else x if m == y else m for m in a)
                    if b in V: c += 1
                K[(x, y)] = c
        best = sorted(K.items(), key=lambda kv: -kv[1])[:4]
        # (c)
        Rk = [sum(1 for a in seqs if not near(N, a[k], a[k + 1])) for k in range(N - 1)]
        # (d)
        half = N // 2
        left = lambda m: 2 * m <= N
        sig = {}; pairs = {}
        for a in seqs:
            s = tuple(m for m in a if left(m)); r = tuple(m for m in a if not left(m))
            sig[s] = sig.get(s, 0) + 1; pairs[(s, r)] = pairs.get((s, r), 0) + 1
        print("N", N, "a", len(seqs))
        print("  affine rank of time vectors: Q", ranks[1000003], "F2", ranks[2], "F3", ranks[3], "(max", N - 1, ")")
        print("  best time-exchange pairs K(x,y):", [(k, v, "%.3f" % (v / len(seqs))) for k, v in best])
        print("  R(k) commuting consecutive pairs at steps k,k+1:", Rk)
        print("  two chains: #left orders", len(sig), "of", __import__("math").factorial(half),
              " #(sigma,rho)", len(pairs), " max #shuffles", max(pairs.values()))
        sys.stdout.flush()

main(int(sys.argv[1]) if len(sys.argv) > 1 else 10)
