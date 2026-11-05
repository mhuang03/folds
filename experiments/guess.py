from fractions import Fraction
v=[1,2,4,10,28,96,256,1120,4256,17878,70960,383476,1620328,9167908,47821296,276182312,1481994716,10084180418,55082188120,398874108930,2505681033958,18168130281086,119006527671252,979730153850974]
def rank_null(M):
    M=[[Fraction(x) for x in r] for r in M]; rows=len(M); cols=len(M[0]); r=0
    for c in range(cols):
        p=next((i for i in range(r,rows) if M[i][c]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        for i in range(rows):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        r+=1
    return r,cols
# sum_{i=0..R} sum_{j=0..d} c_ij n^j a(n-i) = 0
for R in range(1,6):
  for d in range(0,6):
    unk=(R+1)*(d+1)
    eqs=[[ (n**j)*v[n-1-i] for i in range(R+1) for j in range(d+1)] for n in range(R+1,len(v)+1)]
    if len(eqs)<unk+3: continue
    r,c=rank_null(eqs)
    if r<c: print("candidate",R,d,len(eqs),unk)
print("done")
