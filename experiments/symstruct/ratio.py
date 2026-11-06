# r(n) = theta(n) / (2 theta(floor(n/2)) theta(ceil(n/2)))  from the OEIS A003407 b-file.
# usage: python3 ratio.py data/b003407.txt 200
from fractions import Fraction
import sys
th = {}
for line in open(sys.argv[1] if len(sys.argv) > 1 else 'data/b003407.txt'):
    a, b = line.split(); th[int(a)] = int(b)
M = int(sys.argv[2]) if len(sys.argv) > 2 else 60
for n in range(2, M + 1):
    d = 2 * th[n // 2] * th[(n + 1) // 2]
    r = Fraction(th[n], d)
    print(n, f"{float(r):.6f}", th[n], d, r if r.denominator < 10**6 else "")
