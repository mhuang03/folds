"""Item 3: prime factorisations of a(1..38), c(1..41); small-prime statistics vs random
integers; 2-adic valuations; primes dividing a(N) on a whole residue class."""
import math, sympy, signal
from common import counts, selfdual

a, s = counts()
c = selfdual()


def fac(n, t=60):
    def h(*_):
        raise TimeoutError
    signal.signal(signal.SIGALRM, h)
    signal.alarm(t)
    try:
        f = sympy.factorint(n)
        signal.alarm(0)
        return f, True
    except TimeoutError:
        f = sympy.factorint(n, limit=10**7)
        return f, False


def show(f):
    return ' * '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(f.items()))


def v(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k


print('== a(N) factorisations ==')
F = {}
for N in sorted(a):
    f, ok = fac(a[N])
    F[N] = f
    big = max(f) if f else 1
    print(f'{N:2d} {show(f)}{"" if ok else "  (partial)"}   [largest p: {len(str(big))} digits]')

print('\n== c(N) (self-dual) factorisations ==')
for N in sorted(c):
    if c[N] == 0:
        continue
    f, ok = fac(c[N], 30)
    print(f'{N:2d} {show(f)}{"" if ok else "  (partial)"}')

print('\n== symmetric s(N) = A003407 ==')
for N in sorted(s):
    f, ok = fac(s[N], 30)
    print(f'{N:2d} {show(f)}')

# small primes: fraction of N in 6..38 with p | a(N), vs 1/p for random integers;
# but a(N) is always even, so for odd p compare with 1/p.
print('\n== small primes: #{6<=N<=38 : p | a(N)} vs expected 33/p ==')
Ns = [N for N in a if N >= 6]
for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
    hits = [N for N in Ns if a[N] % p == 0]
    print(f'p={p:2d} hits={len(hits):2d} expected={len(Ns)/p:5.2f} (prob of >=hits Binomial) '
          f'N={hits}')
# mean number of distinct prime factors below 1000 vs random (Mertens: sum 1/p)
cnt = [sum(1 for p in sympy.primerange(3, 1000) if a[N] % p == 0) for N in Ns]
exp_ = sum(1 / p for p in sympy.primerange(3, 1000))
print(f'mean #odd primes<1000 dividing a(N): {sum(cnt)/len(cnt):.3f}, random: {exp_:.3f}')
# smoothness: log of largest prime factor / log a
print('\nlog(largest prime)/log a(N):')
print(' '.join(f'{N}:{math.log(max(F[N]))/math.log(a[N]):.2f}' for N in Ns))
# Dickman rho reference: P(largest prime factor <= x^u)...
print('\n== 2-adic valuations ==')
print('N  v2(a) v2(c) a mod 8  c mod 8  a mod 16 c mod 16')
for N in sorted(a):
    if N >= 2:
        print(N, v(a[N], 2), v(c[N], 2) if c[N] else 'inf', a[N] % 8, c[N] % 8,
              a[N] % 16, c[N] % 16)
from collections import Counter
print('distribution of v2(a(N)), N=2..38:', sorted(Counter(v(a[N], 2) for N in a if N >= 2).items()))
print('random even integer: P(v2=k) = 2^-k ; expected counts for 37 terms:',
      [round(37 * 2**-k, 1) for k in range(1, 8)])

print('\n== primes p <= 50 dividing a(N) for all N >= N0 in a residue class mod q (q <= 12) ==')
found = False
for p in sympy.primerange(2, 50):
    for q in range(1, 13):
        for r in range(q):
            NN = [N for N in a if N % q == r and N >= 6]
            if len(NN) >= 3 and all(a[N] % p == 0 for N in NN):
                if p == 2:
                    continue
                print('p', p, 'q', q, 'r', r, NN); found = True
# also powers of 2 beyond what mod 4 gives
for k in (3, 4):
    for q in range(1, 13):
        for r in range(q):
            NN = [N for N in a if N % q == r and N >= 6]
            if len(NN) >= 3 and all(a[N] % 2**k == 0 for N in NN):
                print('2^%d' % k, 'q', q, 'r', r, NN); found = True
print('none' if not found else '')
