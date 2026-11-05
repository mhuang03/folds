"""Does every valid sequence contain a decreasing subsequence of length lg(M) whose
consecutive values satisfy a halving rule?  Rules tested (x = earlier, y = later, y < x):
  h0: 2y <= x          h1: 2y <= x + 1        h2: 2y + 1 <= x
  g0: mirror rule on gaps g = M - v:  g_y >= 2 g_x  (gaps double)
  any: plain decreasing (LDS)"""
from common import *
import sys
rules = {
    'h0': lambda x, y, M: 2*y <= x,
    'h1': lambda x, y, M: 2*y <= x + 1,
    'h2': lambda x, y, M: 2*y + 1 <= x,
    'g0': lambda x, y, M: (M - y) >= 2*(M - x),
    'g1': lambda x, y, M: (M - y) >= 2*(M - x) - 1,
    'any': lambda x, y, M: y < x,
    'yinWx': lambda x, y, M: abs(x-y) <= min(x-1, M-1-x),
    'youtWx': lambda x, y, M: abs(x-y) > min(x-1, M-1-x),
    'xinWy': lambda x, y, M: abs(x-y) <= min(y-1, M-1-y),
    'xoutWy': lambda x, y, M: abs(x-y) > min(y-1, M-1-y),
}
def longest(a, M, rule):
    best = [1]*len(a)
    for j in range(len(a)):
        for i in range(j):
            if a[j] < a[i] and rule(a[i], a[j], M) and best[i] + 1 > best[j]:
                best[j] = best[i] + 1
    return max(best)
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1
    mins = {k: 99 for k in rules}
    for a in A:
        a = list(a)
        for k, r in rules.items():
            mins[k] = min(mins[k], longest(a, M, r))
    print(N, 'lg M =', lg(M), mins, flush=True)
