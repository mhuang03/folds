# Doubling behaviour of r(n) = theta(n) / (2 theta(floor(n/2)) theta(ceil(n/2))).
# Prints max |r(2n) - r(n)| and max |r(2n+1) - (r(n) + r(n+1))/2| over dyadic ranges, and
# r at x * 2^j for a few x (the conjectured log-periodic limit Phi).
from fractions import Fraction
th = {}
for line in open('data/b003407.txt'):
    a, b = line.split(); th[int(a)] = int(b)
def r(n): return th[n] / (2 * th[n // 2] * th[(n + 1) // 2])
M = max(th)
for lo in (8, 16, 32, 64):
    hi = min(2 * lo, M // 2)
    e1 = max(abs(r(2 * n) - r(n)) for n in range(lo, hi))
    e2 = max(abs(r(2 * n + 1) - (r(n) + r(n + 1)) / 2) for n in range(lo, hi) if 2 * n + 1 <= M)
    print(f"n in [{lo},{hi}): max|r(2n)-r(n)| = {e1:.2e}   max|r(2n+1)-avg| = {e2:.2e}")
print("min r(n), n in [16,200]:", min((r(n), n) for n in range(16, M + 1)))
print("max r(n), n in [16,200]:", max((r(n), n) for n in range(16, M + 1)))
for x in (3, 5, 7, 9, 11, 13, 15):
    print(f"x={x}:", [(x * 2**j, round(r(x * 2**j), 6)) for j in range(6) if x * 2**j <= M])
# theta(n)^(1/n) along doubling chains
import math
for x in (3, 4, 5, 6, 7):
    print(f"log(theta)/n along {x}*2^j:", [round(math.log(th[x * 2**j]) / (x * 2**j), 5) for j in range(6) if x * 2**j <= M])
