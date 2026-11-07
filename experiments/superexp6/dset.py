"""Enumerate doubling sets: c:[0,N]->Z, c(0)=0, increments in {0,1},
c(2x+1)=c(x)+c(x+1) (2x+1<=N), c(x)+c(N-x)=p.  Each gives a split a(N) >= 2 a(p) a(N-p)."""
import sys
def search(N):
    res = []
    c = [0]*(N+1)
    def ok(i):
        # check all constraints involving only indices <= i
        # doubling with 2x+1 == i
        if i % 2 == 1:
            x = (i-1)//2
            if c[i] != c[x] + c[x+1]: return False
        return True
    def rec(i):
        if i > N:
            p = c[N]
            if all(c[x] + c[N-x] == p for x in range(N+1)):
                res.append(tuple(c))
            return
        for e in (0, 1):
            c[i] = c[i-1] + e
            if ok(i):
                # mirror partial: c(x)+c(N-x)=p unknown p; skip
                rec(i+1)
    rec(1)
    return res
for N in range(2, int(sys.argv[1])+1):
    r = search(N)
    ps = sorted(set(t[-1] for t in r))
    nontriv = [p for p in ps if 0 < p < N]
    print(N, nontriv, len(r))
