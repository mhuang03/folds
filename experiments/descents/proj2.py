"""First-occurrence projection d of valid a under m -> floor(m/2).  Collect: des/LDS drop,
and the distribution of step imbalances (L-R in the window) of d, split by half."""
from common import *
import sys
from collections import Counter
def proj(a, N):
    Np = (N-1)//2
    d = []; seen = set()
    for m in a:
        y = m//2
        if 1 <= y <= Np and y not in seen:
            seen.add(y); d.append(y)
    return d
def imb(N, d):
    S = set(); out = []
    for m in d:
        r = min(m-1, N-m)
        L = sum((m-k) in S for k in range(1, r+1)); R = sum((m+k) in S for k in range(1, r+1))
        half = 'L' if 2*m < N+1 else ('R' if 2*m > N+1 else 'C')
        out.append((half, L-R)); S.add(m)
    return out
for N in range(int(sys.argv[1]), int(sys.argv[2])+1):
    A = load(N); Np = (N-1)//2
    c1 = Counter(); c2 = Counter()
    for a in A:
        a = list(a); d = proj(a, N)
        c1[(des(a)-des(d), lds(a)-lds(d), lis(a)-lis(d))] += 1
        for h, x in imb(Np, d): c2[(h, x)] += 1
    print(N, 'drops(des,lds,lis) min:', min(k[0] for k in c1), min(k[1] for k in c1), min(k[2] for k in c1))
    print('   imbalance', sorted(c2.items()))
