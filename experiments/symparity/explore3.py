"""Test: with K = floor((N+1)/4), the first K panels all have one parity and the last K
panels all have the other.  Also: f(N) = min over sequences of the length of the longest
constant-parity prefix; g(N) = min over pairs p<q, a_p = a_q mod 2, of max(p-1, N-q)."""
import sys
from apfree import enum

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for N in range(2, Nmax + 1):
    L = enum(N)
    K = (N + 1) // 4
    ok = all(len({w[t] % 2 for t in range(K)}) <= 1 and
             len({w[t] % 2 for t in range(N - K, N)}) <= 1 and
             (K == 0 or w[0] % 2 != w[-1] % 2) for w in L)
    def pref(w):
        t = 1
        while t < N and w[t] % 2 == w[0] % 2:
            t += 1
        return t
    f = min(pref(w) for w in L)
    g = min(max(p, N - 1 - q) for w in L for p in range(N) for q in range(p + 1, N)
            if (w[p] - w[q]) % 2 == 0) if N > 2 else None
    print(f'N={N:2d} K={K} prefix/suffix claim: {ok}   f(N)={f}   g(N)={g}')
