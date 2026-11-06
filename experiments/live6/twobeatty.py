"""twobeatty.py N u: search two-sided Beatty copies
     X = {floor((A i + B)/D) : 1 <= i <= L}  +  {N + 1 - floor((A' j + B')/D) : 1 <= j <= R}
with first element u on the left and u on the right (the symmetric pair (u, N+1-u)), D <= 4,
that are inward window copies of odd size."""
import sys
from math import floor
from twoside import is_inward_copy

N, u = int(sys.argv[1]), int(sys.argv[2])
found = set()
for D in (1, 2, 3, 4, 6, 8):
    for A in range(u * D, (u + 1) * D + 1):
        for B in range(-A, D):
            if (A + B) // D != u:
                continue
            for A2 in range(u * D, (u + 1) * D + 1):
                for B2 in range(-A2, D):
                    if (A2 + B2) // D != u:
                        continue
                    for L in range(2, N // u + 1):
                        left = [(A * i + B) // D for i in range(1, L + 1)]
                        if left[-1] > N:
                            break
                        for R in range(max(1, L - 3), L + 3):
                            if (L + R) % 2 == 0:
                                continue
                            right = [N + 1 - (A2 * j + B2) // D for j in range(R, 0, -1)]
                            if right[0] <= left[-1]:
                                continue
                            X = tuple(left + right)
                            if X in found:
                                continue
                            if is_inward_copy(N, list(X)):
                                found.add(X)
                                print(len(X), (A, B, D), (A2, B2, D), L, R, X, flush=True)
