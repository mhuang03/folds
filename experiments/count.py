import sys
from functools import lru_cache
def counts(N):
    full=(1<<N)-1
    # DP over subsets: number of valid orderings reaching set S (order-independent condition depends only on S and m)
    def ok(S,m,sym):
        D=min(m-1,N-m)
        if sym:
            return all(((S>>(m-d-1))&1)==((S>>(m+d-1))&1) for d in range(1,D+1))
        return sum((S>>(m-d-1))&1 for d in range(1,D+1))==sum((S>>(m+d-1))&1 for d in range(1,D+1))
    res=[]
    for sym in (True,False):
        dp={0:1}
        for _ in range(N):
            nd={}
            for S,c in dp.items():
                for m in range(1,N+1):
                    if not S>>(m-1)&1 and ok(S,m,sym):
                        T=S|1<<(m-1); nd[T]=nd.get(T,0)+c
            dp=nd
        res.append(dp.get(full,0))
    return res
for N in range(1,int(sys.argv[1])+1):
    print(N,*counts(N),flush=True)
