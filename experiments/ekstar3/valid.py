import sys, itertools
def imb(N,B,m):
    r=min(m-1,N-m); return sum(1 for x in B if m-r<=x<m)-sum(1 for x in B if m<x<=m+r)
def valid(N,t):
    for p in itertools.permutations(t):
        if all(imb(N,p[:i],p[i])==0 for i in range(3)): return True
    return False
N=int(sys.argv[1]); nv=ni=0
for line in sys.stdin:
    if line.startswith('R'):
        n,a,b,c=map(int,line.split()[1:])
        if valid(N,(a,b,c)): nv+=1
        else: ni+=1
print(N,'valid',nv,'invalid',ni)
