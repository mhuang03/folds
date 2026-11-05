"""denoms.py K: common denominator of the quasi-polynomial T(N,K) and of each coefficient."""
import sys
import json
from fractions import Fraction as Fr
from math import lcm

K = int(sys.argv[1])
comp = json.load(open(f'components_{K}.json'))
tot = 1
for j in sorted(comp, key=int, reverse=True):
    D = lcm(*[Fr(x).denominator for g in comp[j].values() for x in g])
    tot = lcm(tot, D)
    print(f'c_{j}: common denominator {D}', ' components d =', sorted(map(int, comp[j])))
print('overall common denominator', tot)
