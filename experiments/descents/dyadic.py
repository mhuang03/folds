"""Dyadic first-occurrence projections.  d_j(a) = order of first occurrence of the blocks
B_{j,y} = [2^j y, 2^j (y+1) - 1], y = 1 .. M_j - 1 (M = N+1, M_j = floor(M / 2^j)).
Check (*): the last ascending run of d_j contains no two siblings {2y, 2y+1} (y >= 1),
and collect the minimum of z_{i+1} - 2 z_i over consecutive members of the last run.
Also check des(d_j) >= des(d_{j+1}) + 1 and lds(d_j) >= lds(d_{j+1}) + 1."""
from common import *
import sys
from collections import Counter
def dj(a, M, j):
    Mj = M >> j; seen = set(); d = []
    for m in a:
        y = m >> j
        if 1 <= y <= Mj - 1 and y not in seen:
            seen.add(y); d.append(y)
    return d
def lastrun(d):
    i = len(d) - 1
    while i > 0 and d[i-1] < d[i]: i -= 1
    return d[i:]
if __name__ == "__main__":
  for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
      A = load(N); M = N + 1
      bad = Counter(); gap = Counter(); drops = Counter()
      for a in A:
          a = list(a)
          J = lg(M)
          ds = [dj(a, M, j) for j in range(J)]
          for j in range(J):
              d = ds[j]
              lr = lastrun(d)
              sib = any(lr[i] % 2 == 0 and lr[i] + 1 == lr[i+1] and lr[i] >= 2 for i in range(len(lr)-1))
              if sib: bad[j] += 1
              for i in range(len(lr) - 1):
                  gap[(j, min(lr[i+1] - 2*lr[i], 3))] += 1
              if j + 1 < J:
                  drops[(j, des(d) - des(ds[j+1]) >= 1, lds(d) - lds(ds[j+1]) >= 1)] += 1
      print(N, 'sibling violations by level:', dict(bad))
      print('   z_{i+1}-2z_i (capped 3):', sorted(gap.items()))
      print('   drops:', sorted(drops.items()))
