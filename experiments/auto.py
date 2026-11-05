import itertools
def semi(p,N):
    S=set()
    for m in p:
        D=min(m-1,N-m)
        if sum((m-d) in S for d in range(1,D+1))!=sum((m+d) in S for d in range(1,D+1)): return False
        S.add(m)
    return True
for N in range(3,9):
    V=set(p for p in itertools.permutations(range(1,N+1)) if semi(p,N))
    G=[]
    for s in itertools.permutations(range(1,N+1)):
        if all(tuple(s[x-1] for x in p) in V for p in V): G.append(s)
    print(N,len(V),len(G),G[:8])
