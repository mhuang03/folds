"""Attempts 6, 7: identity (A)
   a(N) = 2a(fl N/2)a(ce N/2) + 2 sum_{d|N odd, 3<=d<N} a(jN/d)a((j+1)N/d) + I(N),  d = 2j+1.
I(N), its share, 2- and 3-adic valuations of a(N), a(N)/2, I(N)."""
from common import A

def v(p, x):
    k = 0
    while x and x % p == 0:
        x //= p; k += 1
    return k

print("N  v2(a) v3(a) v2(I) v3(I)  main/a   divsum/a      I/a")
for N in range(2, 39):
    main = 2 * A[N // 2] * A[(N + 1) // 2]
    ds = 0
    for d in range(3, N, 2):
        if N % d == 0:
            j = (d - 1) // 2
            ds += 2 * A[j * N // d] * A[(j + 1) * N // d]
    I = A[N] - main - ds
    print("%2d   %d     %d     %s     %s    %.3e %.3e %.6f" % (
        N, v(2, A[N]), v(3, A[N]), v(2, I) if I else '-', v(3, I) if I else '-',
        main / A[N], ds / A[N], I / A[N]))
print("v2(a(N)) by N mod 4:")
for r in range(4):
    print(r, [v(2, A[N]) for N in range(2, 39) if N % 4 == r])
print("a(N)/2 mod 2, N = 0 mod 4:", [(A[N] // 2) % 2 for N in range(4, 39, 4)])
print("a(N)/2 mod 2, N = 1 mod 4:", [(A[N] // 2) % 2 for N in range(5, 39, 4)])
print("a(N)/2 mod 2, N = 2 mod 4:", [(A[N] // 2) % 2 for N in range(2, 39, 4)])
print("a(N)/4 mod 2, N = 3 mod 4:", [(A[N] // 4) % 2 for N in range(3, 39, 4)])
