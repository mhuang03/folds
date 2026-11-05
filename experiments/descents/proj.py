"""Test the 2-to-1 projection m -> floor(m/2) (pairs {2y,2y+1}, y = 1..floor((N-1)/2)):
is the first/last-occurrence order valid in the smaller world, and does des / LDS drop?"""
from common import *
import sys
for N in range(3, int(sys.argv[1])+1):
    A = load(N); Np = (N-1)//2
    stats = {}
    for a in A:
        a = list(a)
        ys = [m//2 for m in a if 1 <= m//2 <= Np]
        for mode in ('first', 'last'):
            d = []
            it = ys if mode == 'first' else ys[::-1]
            for y in it:
                if y not in d: d.append(y)
            if mode == 'last': d = d[::-1]
            v = valid(Np, d)
            key = (mode, v, des(d) - des(a), lds(d) - lds(a))
            stats[key] = stats.get(key, 0) + 1
    print(N, sorted(stats.items()))
