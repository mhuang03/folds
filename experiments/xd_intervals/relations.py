"""Exact relations in the wall table W(n,B) (out/wall_rows.txt, B = n..2n+2) and in the
offset table a(N;0,be) (out/row0.txt).  Prints which identities hold on all the data."""
import os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
W = {}
for l in open(os.path.join(HERE, 'out', 'wall_rows.txt')):
    n, r = l.split(':'); n = int(n)
    for i, v in enumerate(r.split()):
        W[(n, n + i)] = int(v)
NW = max(n for n, _ in W)
A = {}
for l in open(os.path.join(HERE, 'out', 'row0.txt')):
    n, r = l.split(':'); n = int(n)
    for b, v in enumerate(r.split()):
        A[(n, b)] = int(v)
NA = max(n for n, _ in A)

def H(N):                       # half-line count, from the wall table
    return 1 if N == 0 else W[(N // 2, N)] if N >= 2 else 1

print("== half-line H(N) = a(N;0,inf) from the offset table vs the wall reduction W(N//2,N)")
print(all(A[(N, N - 1)] == H(N) for N in range(2, NA + 1)), "for 2 <= N <=", NA)
print("H:", [H(N) for N in range(0, 2 * NW + 1)][:50])

print("== H(2n+1) = H(n):", all(H(2 * n + 1) == H(n) for n in range(1, NW)), "n <", NW)
print("== stabilisation in B: W(n,B)=H(n) at B=n, 2n+1, 2n+2:",
      all(W[(n, n)] == H(n) == W[(n, 2 * n + 1)] == W[(n, 2 * n + 2)] for n in range(2, NW + 1)))

cnt = bad = 0
for n in range(1, NW + 1):
    for j in range(1, n + 1):
        if n <= 2 * j + 1 and (j, n) in W and (n, 2 * j + 1) in W:
            cnt += 1
            if W[(n, 2 * j + 1)] != W[(j, n)]:
                bad += 1; print("  FAIL", n, j)
print("== halving: W(n,2j+1) = W(j,n) for (n-1)/2 <= j <= n:", cnt, "cases,", bad, "failures")

cnt = bad = 0
for j in range(1, NW // 2 + 1):
    n = 2 * j
    if (n, n + 3) in W:
        cnt += 1
        if W[(n, n + 2)] != W[(n, n + 1)] + W[(n, n + 3)]:
            bad += 1
print("== W(2j,2j+2) = W(2j,2j+1) + W(2j,2j+3) [= H(2j) + W(j+1,2j)]:", cnt, "cases,", bad, "failures")

# stabilisation of the offset rows
print("== offset rows: first be with a(N;0,be) = H(N)")
for N in range(2, NA + 1):
    b0 = min(b for b in range(N) if all(A[(N, c)] == A[(N, N - 1)] for c in range(b, N)))
    print("  N=%d: be >= %d   (N-1-be0 = %d)" % (N, b0, N - 1 - b0))

# brute-force search: W(n,B) (B even, n<B<2n) as a +-1/0 combination of <=3 entries with
# smaller n, or the same n and other B
print("== small relations for even B: W(n,B) = sum of <= 3 entries among {W(n',B')} with n' <= n")
def cands(n, B):
    c = []
    for (n2, B2), v in W.items():
        if n2 <= n and (n2, B2) != (n, B) and n2 <= B2 <= 2 * n2 and n2 >= n // 2 - 1 and v > 1:
            c.append(((n2, B2), v))
    return c
for n in range(6, 15):
    for B in range(n + 2, 2 * n + 1, 2):
        t = W[(n, B)]; c = cands(n, B); found = []
        vals = {}
        for k, v in c: vals.setdefault(v, []).append(k)
        for k1, v1 in c:
            if v1 == t: found.append((k1,))
            if t - v1 in vals and t - v1 >= v1:
                for k2 in vals[t - v1]:
                    found.append((k1, k2))
        print("  W(%d,%d)=%d:" % (n, B, t), found[:6])
