"""Exploration: parity of a_k versus a_{N+1-k}; parity balance by position."""
import sys
from apfree import enum

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for N in range(2, Nmax + 1):
    L = enum(N)
    same = [sum(1 for w in L if w[k - 1] % 2 == w[N - k] % 2) for k in range(1, N // 2 + 1)]
    bal = [sum(1 if w[k] % 2 else -1 for w in L) for k in range(N)]
    print(f'N={N:2d} s={len(L):6d} same-parity(a_k,a_N+1-k): {same}')
    print(f'       odd-even by position: {bal}')
