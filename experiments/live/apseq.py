"""apseq.py N1 N2: which cyclic arithmetic progressions a_i = ((s + i d) mod N) + 1 are
semi-symmetric fold sequences?"""
import sys
from math import gcd


def valid(N, a):
    S = set()
    for m in a:
        r = min(m - 1, N - m)
        if sum(1 for d in range(1, r + 1) if (m - d) in S) != \
                sum(1 for d in range(1, r + 1) if (m + d) in S):
            return False
        S.add(m)
    return True


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    good = []
    for d in range(1, N):
        if gcd(d, N) != 1:
            continue
        for s in range(N):
            a = [((s + i * d) % N) + 1 for i in range(N)]
            if valid(N, a):
                good.append((a[0], a[1]))
    print(N, good)
