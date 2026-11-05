"""rule.py: check the "window rule" characterisation of a valid step against the definition.

Step c with earlier points: A of them above c, B below; y_1 > y_2 > ... the ones below
(nearest first), z_1 < z_2 < ... the ones above (nearest first).
  A < B :  valid iff  y_A >= 2c - N > y_{A+1}        (y_0 = +inf); c is then in the right half
                       and its window [2c-N, N] holds all A points above and the A nearest below
  A > B :  valid iff  z_B <= 2c - 1 < z_{B+1}         (z_0 = -inf); mirror image
  A = B :  valid iff  y_B >= 2c - N and z_A <= 2c - 1 (the window holds every earlier point)
Proof: if c is in the left half its window [1, 2c-1] holds all B points below, so it needs B
points above, impossible when A < B; so c is in the right half, whose window [2c-N, N] holds
all A points above, and exactly A points below must lie in [2c-N, c).  A = B: whichever half
c is in, the window already holds all points on one side, so it must hold all on the other.
Consequence: which earlier points lie in the window (the sign matrix) depends only on the order
type of the sequence."""
from itertools import permutations


def ok_def(N, S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S)


def ok_rule(N, S, c):
    ys = sorted((x for x in S if x < c), reverse=True)
    zs = sorted(x for x in S if x > c)
    A, B = len(zs), len(ys)
    if A < B:
        return (A == 0 or ys[A - 1] >= 2 * c - N) and ys[A] < 2 * c - N
    if A > B:
        return (B == 0 or zs[B - 1] <= 2 * c - 1) and zs[B] > 2 * c - 1
    return (B == 0 or (ys[-1] >= 2 * c - N and zs[-1] <= 2 * c - 1))


for N in range(1, 15):
    for S in range(1 << N):
        Sset = {i + 1 for i in range(N) if S >> i & 1}
        for c in range(1, N + 1):
            if c not in Sset:
                assert ok_def(N, Sset, c) == ok_rule(N, Sset, c), (N, Sset, c)
print('window rule == definition for every (S, c), N <= 14')
