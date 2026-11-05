import sys
def run(N):
    full=(1<<N)-1
    def ok(S,m):
        D=min(m-1,N-m)
        return sum((S>>(m-d-1))&1 for d in range(1,D+1))==sum((S>>(m+d-1))&1 for d in range(1,D+1))
    f={full:1}
    for S in range(full-1,-1,-1):
        t=0
        for m in range(1,N+1):
            b=1<<(m-1)
            if not S&b and ok(S,m): t+=f.get(S|b,0)
        f[S]=t
    return f
for N in range(2,int(sys.argv[1])+1):
    f=run(N)
    print(N,f[0],'first:',[f[1<<(m-1)] for m in range(1,N+1)])
