"""Checks the exact decomposition identities on the output of decomp (out/decomp_N.txt,
out/copyJ_N.txt, out/sets_N.txt) and prints the tables of NOTES.txt sections 3-4.

(A) neutral identity  a(N) = sum_{X in E_N} a(|X|) a(N-|X|) + I(N)
    E_N = {evens, odds} ∪ {E_d, E_d^c : d | N odd, 3 <= d < N}
(B) first-copy identity  a(N) = J(N) + sum_{k=2}^{N-1} J(k) C_N(k),
    C_N(k) = sum_{X copy, |X| = k} g(X^c);  J_N(X) = J(|X|) for every copy X;
    g(X) = a(|X|) for every copy X.
usage: python3 check_identities.py NMAX"""
import sys

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 24
A = {}
for line in open("../semi_counts.txt"):
    if line.startswith("#"):
        continue
    p = line.split()
    A[int(p[0])] = int(p[1])

I, J, firstCopy, ncopy, nneu = {}, {}, {}, {}, {}
for N in range(1, NMAX + 1):
    lines = open(f"out/decomp_{N}.txt").read().split("\n")
    h = dict(kv.split("=") for kv in lines[0].split())
    assert int(h["a"]) == A[N]
    I[N], J[N] = int(h["I"]), int(h["J"])
    firstCopy[N] = {}
    ncopy[N] = {}
    nneu[N] = {}
    for l in lines[2:]:
        if not l.strip():
            continue
        k, nc, nn, fn, fc, cm = l.split()
        firstCopy[N][int(k)] = int(fc)
        ncopy[N][int(k)] = int(nc)
        nneu[N][int(k)] = int(nn)

print("(A) neutral identity: N a(N) productPart I(N) I/a")
for N in range(2, NMAX + 1):
    prod = 2 * A[N // 2] * A[(N + 1) // 2]
    for d in range(3, N, 2):
        if N % d == 0:
            j, n = (d - 1) // 2, N // d
            prod += 2 * A[j * n] * A[(j + 1) * n]
    assert prod + I[N] == A[N], N
    # also: the neutral sets found by brute force are exactly E_N, with g = a(|X|), h = a(N-|X|)
    for line in open(f"out/sets_{N}.txt"):
        m, k, g, gi, hh = line.split()
        k = int(k)
        assert int(g) == A[k] and int(hh) == A[N - k] and int(gi) == int(g)
    print(N, A[N], prod, I[N], f"{I[N] / A[N]:.6f}")

print("\n(B) first-copy identity: N J(N) J/a  [k: #copies]")
for N in range(2, NMAX + 1):
    tot = J[N]
    for k in range(2, N):
        fc = firstCopy[N].get(k, 0)
        # fc = sum over copies X of size k of J_N(X) g(X^c); check J_N(X) = J(k), g(X) = a(k)
        if k < N and ncopy[N].get(k, 0):
            for l in open(f"out/copyJ_{N}.txt"):
                p = l.split()
                if int(p[0]) == k:
                    jmin, jmax = int(p[1].split("=")[1]), int(p[2])
                    gmin, gmax = int(p[3].split("=")[1]), int(p[4])
                    assert jmin == jmax == J[k], (N, k, jmin, jmax, J[k])
                    assert gmin == gmax == A[k], (N, k)
        tot += fc
    assert tot == A[N], N
    print(N, J[N], f"{J[N] / A[N]:.4f}", {k: v for k, v in ncopy[N].items() if v})
print("\nall identities verified for N <=", NMAX)
