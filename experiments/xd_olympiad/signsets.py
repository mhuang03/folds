"""Signed subset function gs(S) = sum of signs of valid orderings of S (sign = (-1)^inv of the word).
Per layer: #reachable S, #S with gs != 0, sum |gs|.  Usage: signsets.py Nmax [list N]"""
import sys
from common import *

def gsigned(N):
    L, R = masks(N); pc = lambda x: bin(x).count("1")
    g = {0: 1}; gs = {0: 1}
    layers = [{0: (1, 1)}]
    cur = {0: (1, 1)}
    for k in range(N):
        nxt = {}
        for S, (c, cs) in cur.items():
            for m in range(1, N + 1):
                b = 1 << (m - 1)
                if S & b or pc(S & L[m]) != pc(S & R[m]): continue
                sg = -1 if pc(S >> m) & 1 else 1
                o = nxt.get(S | b, (0, 0))
                nxt[S | b] = (o[0] + c, o[1] + sg * cs)
        layers.append(nxt); cur = nxt
    return layers

if __name__ == "__main__":
    Nmax = int(sys.argv[1])
    for N in range(2, Nmax + 1):
        lay = gsigned(N)
        print("N", N, "D", lay[N][(1 << N) - 1][1])
        print("  reach  ", [len(l) for l in lay])
        print("  nonzero", [sum(1 for v in l.values() if v[1]) for l in lay])
        print("  sum|gs|", [sum(abs(v[1]) for v in l.values()) for l in lay])
        if len(sys.argv) > 2 and int(sys.argv[2]) == N:
            for k, l in enumerate(lay):
                for S, v in sorted(l.items()):
                    if v[1]:
                        print("   ", k, [i + 1 for i in range(N) if S >> i & 1], v)
