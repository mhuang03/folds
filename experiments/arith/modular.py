"""p-adic / modular / divisibility scan of a(N)."""
from math import gcd
from sympy import factorint, primerange
from data import a

Ns = sorted(a)


def v(p, x):
    k = 0
    while x % p == 0:
        x //= p
        k += 1
    return k


print("N  v2  v3  v5  v7  factorization")
for N in Ns:
    f = factorint(a[N], limit=10**6)
    print(N, v(2, a[N]), v(3, a[N]), v(5, a[N]), v(7, a[N]), dict(f))

print("\nresidues")
for m in [3, 4, 5, 7, 8, 9, 11, 13, 16, 32, 64]:
    print(f"mod {m:3d}:", [a[N] % m for N in Ns])

print("\na(p) mod p, a(p-1) mod p, a(p+1) mod p for primes p<=33")
for p in primerange(2, 34):
    print(p, a[p] % p, a[p - 1] % p if p > 1 else None, a[p + 1] % p if p + 1 in a else None)

print("\nN | a(N)?  and  a(N) mod N")
print([(N, a[N] % N) for N in Ns])

print("\ngcd(a(N), a(N-1)), gcd(a(2n),a(n))")
print([(N, gcd(a[N], a[N - 1])) for N in Ns[1:]])
print([(n, gcd(a[2 * n], a[n]), a[2 * n] % a[n]) for n in Ns if 2 * n in a])

print("\nratios a(N)/a(N-1)")
for N in Ns[1:]:
    print(N, N % 2, N % 3, round(a[N] / a[N - 1], 4), round(a[N] / a[N - 1] / N, 4))

print("\nodd part of a(N)/2^v2 mod 4, mod 8")
print([(N, (a[N] >> v(2, a[N])) % 8) for N in Ns])
