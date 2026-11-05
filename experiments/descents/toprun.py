"""Find valid prefixes with <= R ascending runs (R given) in world N whose set contains the
top block [N-n+1, N].  DFS.  usage: toprun.py N n R [limit]"""
from common import *
import sys
N, n, R = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
lim = int(sys.argv[4]) if len(sys.argv) > 4 else 5
need = set(range(N - n + 1, N + 1)); found = []
def rec(seq, S, runs):
    if need <= S:
        found.append(list(seq)); return len(found) >= lim
    for m in range(1, N + 1):
        if m in S: continue
        nr = runs + (1 if seq and m < seq[-1] else 0)
        if nr > R or not valid_step(N, S, m): continue
        seq.append(m); S.add(m)
        if rec(seq, S, nr): return True
        seq.pop(); S.discard(m)
    return False
rec([], set(), 1)
for f in found:
    out = []
    for i, x in enumerate(f):
        if i and x < f[i-1]: out.append('|')
        out.append(str(x))
    print(' '.join(out))
