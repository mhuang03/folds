"""Print the largest-f bisimulation classes of layer k (small N): python3 dumpcls.py N k"""
import sys
from collections import defaultdict
from common import tables, bisimF, bits

N = int(sys.argv[1])
k = int(sys.argv[2])
valid, g, f = tables(N)
cls = bisimF(N, valid, g, f)
C = defaultdict(list)
for s in range(1 << N):
    if bin(s).count('1') == k and g[s] and f[s]:
        C[cls[s]].append(s)
sizes = defaultdict(int)
for L in C.values():
    sizes[len(L)] += 1
print('class size histogram', sorted(sizes.items()))
big = sorted(C.values(), key=lambda L: -f[L[0]] * (len(L) > 2))
for L in big[:15]:
    print('f=', f[L[0]], 'size', len(L))
    for s in L[:8]:
        print('   ', bits(s, N), 'g=', g[s])
