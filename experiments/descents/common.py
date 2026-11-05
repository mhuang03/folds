import numpy as np, os, bisect
SP = '/tmp/claude-0/-home-user-folds/bd994c7a-a824-526f-8ce9-3cfdb91d329e/scratchpad/seqs'
def load(N):
    a = np.fromfile(f'{SP}/s{N}.bin', dtype=np.uint8)
    return a.reshape(-1, N).astype(int)
def valid_step(N, S, m):
    r = min(m-1, N-m)
    return sum((m-d) in S for d in range(1, r+1)) == sum((m+d) in S for d in range(1, r+1))
def valid(N, a):
    S = set()
    for m in a:
        if not valid_step(N, S, m): return False
        S.add(m)
    return True
def des(a): return sum(a[i] > a[i+1] for i in range(len(a)-1))
def lis(a):
    t = []
    for x in a:
        i = bisect.bisect_left(t, x)
        if i == len(t): t.append(x)
        else: t[i] = x
    return len(t)
def lds(a): return lis([-x for x in a])
def lg(x): return x.bit_length()-1
