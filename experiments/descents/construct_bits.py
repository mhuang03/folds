"""Candidate constructions: run index from the number of 1-bits in the first K binary digits of
a point x(m) attached to panel m, K = lg(M) + 1.  Order = by (run, m).  Test validity."""
from common import *
from fractions import Fraction as Fr
import sys
def valid_fast(N, a):
    pos = [0] * (N + 2)
    for i, m in enumerate(a): pos[m] = i
    for m in range(1, N + 1):
        r = min(m - 1, N - m); t = pos[m]
        if sum(pos[m - d] < t for d in range(1, r + 1)) != sum(pos[m + d] < t for d in range(1, r + 1)):
            return False
    return True
def bits(x, K):
    c = 0
    for _ in range(K):
        x *= 2
        if x >= 1: c += 1; x -= 1
    return c
maps = {
    'm/M': lambda m, N: Fr(m, N + 1),
    '(m-1/2)/N': lambda m, N: Fr(2 * m - 1, 2 * N),
    '(m+1/2)/(N+2)': lambda m, N: Fr(2*m + 1, 2 * (N + 2)),
    'm/(N+2)': lambda m, N: Fr(m, N + 2),
    '(m-1)/(N-1)': lambda m, N: Fr(m - 1, max(N - 1, 1)),
}
def _main():
  for name, f in maps.items():
      ok = []
      for N in range(1, int(sys.argv[1]) + 1):
          M = N + 1; K = lg(M) + 1
          for sgn in (1,):
              rho = {m: K - bits(f(m, N), K) for m in range(1, N + 1)}
              a = sorted(range(1, N + 1), key=lambda m: (rho[m], m))
              if valid_fast(N, a): ok.append(N)
      print(name, ok)

if __name__ == '__main__': _main()
