import sys, math
from pair import kappa, radius, w
from fractions import Fraction
from math import factorial
sys.path.insert(0, "../structure")
A = [1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
     47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
     2505681033958, 18168130281086, 119006527671252, 979730153850974,
     6564449510287388, 55581983250573500, 413109755332919448]

N = int(sys.argv[1])
print("kappa(m,m') table, N =", N)
print("     " + " ".join("%6d" % j for j in range(1, N + 1)))
for m in range(1, N + 1):
    row = []
    for mp in range(1, N + 1):
        if mp <= m:
            row.append("      ")
        else:
            row.append("%6.3f" % float(kappa(N, m, mp)))
    print("%4d " % m + " ".join(row))
