import itertools
def neutral(N,X):
    for m in range(1,N+1):
        r=min(m-1,N-m)
        if sum(1 for x in X if m-r<=x<m)!=sum(1 for x in X if m<x<=m+r): return False
    return True
for N in range(1,17):
    for mask in range(1<<N):
        X=[i+1 for i in range(N) if mask>>i&1]; s=len(X)
        if not neutral(N,X): continue
        xs=set(X)
        def cnt(t): return (t//N)*s+sum(1 for x in X if x<=t%N)
        for k in range(3*N):
            assert cnt(2*k+1)==cnt(k)+cnt(k+1)
        mu=min(s,N-s)
        for t in range(N):
            h=N*cnt(t)-s*t
            assert -mu<=h<=mu,(N,X,t,h)
        if 0<s<N: assert 3*s>=N
print("ok")
