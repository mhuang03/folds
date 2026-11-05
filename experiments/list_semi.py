import sys, itertools
def semi(p,N):
    S=set()
    for m in p:
        D=min(m-1,N-m)
        if sum((m-d) in S for d in range(1,D+1))!=sum((m+d) in S for d in range(1,D+1)): return False
        S.add(m)
    return True
N=int(sys.argv[1])
V=[p for p in itertools.permutations(range(1,N+1)) if semi(p,N)]
print(len(V))
for p in V: print(''.join(map(str,p)))
