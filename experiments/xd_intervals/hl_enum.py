# enumerate the left-half orders of the half-line model H(N) (reduction of hl.c)
import sys
def seqs(N):
    n=N//2; out=[]
    def ok(S,m,k):
        l=sum(1 for i in S if i<m); r=sum(1 for i in S if m<i<=min(n,2*m-1))
        ex=max(0,2*m-1-max(n,N-k))
        return l==r+ex
    def rec(seq,S):
        if len(seq)==n: out.append(tuple(seq)); return
        k=len(seq)+1
        for m in range(1,n+1):
            if m not in S and ok(S,m,k):
                S.add(m); seq.append(m); rec(seq,S); seq.pop(); S.remove(m)
    rec([],set()); return out
if __name__=="__main__":
    for N in map(int,sys.argv[1:]):
        s=seqs(N); print("N=%d H=%d"%(N,len(s)))
        for x in s: print("  "," ".join(map(str,x)))
