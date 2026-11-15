#!/usr/bin/env python3
"""Brute-force checks for small N (independent of the C programs).
 1. swap criterion: for a valid sequence, exchanging adjacent steps p,p+1 gives a valid
    sequence iff the two panels are independent (each outside the other's window);
    also the 'local' criterion on (S,m,m') for ALL sets S.
 2. K(N) by union-find over valid sequences; classes = intervals of weak order; each class
    has unique top/bottom; left-half order and right-half order constant on a class.
 3. Z(N) = number of rigid sequences = singleton classes.
"""
import sys, itertools
from collections import defaultdict

def reach(N,m): return min(m-1,N-m)
def inwin(N,m,x): return x!=m and abs(x-m)<=reach(N,m)
def indep(N,x,y): return x!=y and not inwin(N,x,y) and not inwin(N,y,x)
def valid_step(N,S,m):
    r=reach(N,m)
    return sum(1 for d in range(1,r+1) if m-d in S)==sum(1 for d in range(1,r+1) if m+d in S)
def valid(N,a):
    S=set()
    for m in a:
        if not valid_step(N,S,m): return False
        S.add(m)
    return True
def gen(N):
    out=[]
    def rec(a,S):
        if len(a)==N: out.append(tuple(a)); return
        for m in range(1,N+1):
            if m not in S and valid_step(N,S,m):
                a.append(m); S.add(m); rec(a,S); a.pop(); S.remove(m)
    rec([],set()); return out
def invset(a): return frozenset((x,y) for i,x in enumerate(a) for y in a[i+1:] if x>y)

def main(maxN):
    for N in range(1,maxN+1):
        V=gen(N); Vs=set(V); idx={a:i for i,a in enumerate(V)}
        # 1a. sequence-level criterion
        bad=0
        for a in V:
            for p in range(N-1):
                b=list(a); b[p],b[p+1]=b[p+1],b[p]; b=tuple(b)
                if (b in Vs)!=indep(N,a[p],a[p+1]): bad+=1
        # 1b. local criterion for all S (N<=10)
        badloc=0; nloc=0
        if N<=10:
            for mask in range(1<<N):
                S={i+1 for i in range(N) if mask>>i&1}
                for m in range(1,N+1):
                    if m in S or not valid_step(N,S,m): continue
                    S1=S|{m}
                    for m2 in range(1,N+1):
                        if m2 in S1 or not valid_step(N,S1,m2): continue
                        nloc+=1
                        sw = valid_step(N,S,m2) and valid_step(N,S|{m2},m)
                        if sw!=indep(N,m,m2): badloc+=1
        # 2. union-find
        par=list(range(len(V)))
        def find(x):
            while par[x]!=x:
                par[x]=par[par[x]]; x=par[x]
            return x
        deg=[0]*len(V)
        for a in V:
            for p in range(N-1):
                if indep(N,a[p],a[p+1]):
                    deg[idx[a]]+=1
                    b=list(a); b[p],b[p+1]=b[p+1],b[p]
                    ra,rb=find(idx[a]),find(idx[tuple(b)])
                    if ra!=rb: par[ra]=rb
        cls=defaultdict(list)
        for a in V: cls[find(idx[a])].append(a)
        K=len(cls); Z=sum(1 for d in deg if d==0)
        h=N//2
        okLR=True; okInt=True
        for c in cls.values():
            L={tuple(x for x in a if x<=h) for a in c}; R={tuple(x for x in a if x>h) for a in c}
            if len(L)!=1 or len(R)!=1: okLR=False
            invs=[invset(a) for a in c]
            mn=min(invs,key=len); mx=max(invs,key=len)
            if not all(mn<=s<=mx for s in invs): okInt=False
            if N<=8:   # the class is the WHOLE weak-order interval [mn,mx] of S_N
                cnt=0
                for b in itertools.permutations(range(1,N+1)):
                    s=invset(b)
                    if mn<=s<=mx: cnt+=1
                if cnt!=len(c): okInt=False
        sizes=sorted(len(c) for c in cls.values())
        print(f"N={N} a={len(V)} swapcrit_bad={bad} local_bad={badloc}/{nloc} K={K} Z={Z} "
              f"singletons={sum(1 for s in sizes if s==1)} maxclass={sizes[-1]} "
              f"LRconst={okLR} interval={okInt}")
        sys.stdout.flush()
if __name__=="__main__": main(int(sys.argv[1]) if len(sys.argv)>1 else 9)
