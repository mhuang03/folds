# Check a(N) = sum_{|S|=k} g(S) g([N]\S) for every k (consequence of reversal invariance),
# where g(S) = number of semi-symmetric orderings of S as a prefix.
import sys
from itertools import combinations
def g_all(N):
    full=(1<<N)-1
    def ok(S,m):
        D=min(m-1,N-m)
        return sum((S>>(m-d-1))&1 for d in range(1,D+1))==sum((S>>(m+d-1))&1 for d in range(1,D+1))
    g=[0]*(1<<N); g[0]=1
    for S in range(full):
        if g[S]:
            for m in range(1,N+1):
                b=1<<(m-1)
                if not S&b and ok(S,m): g[S|b]+=g[S]
    return g
for N in range(1,int(sys.argv[1])+1):
    g=g_all(N); full=(1<<N)-1
    sums=[sum(g[S]*g[full^S] for S in range(1<<N) if bin(S).count('1')==k) for k in range(N+1)]
    print(N,g[full],set(sums)=={g[full]})
