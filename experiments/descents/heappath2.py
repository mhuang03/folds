"""Mixed 'doubling-tree' paths: longest path v_1, v_2, ... with v_{i+1} a 'child' of v_i
(several definitions of children via the doubling map) and v_{i+1} placed BEFORE v_i.
Min over valid sequences, compared with lg(M)."""
from common import *
import sys
def longest(N, tau, kids):
    memo = {}
    def f(v):
        if v in memo: return memo[v]
        memo[v] = 1; b = 1
        for w in kids(v):
            if 1 <= w <= N and w != v and tau[w] < tau[v]: b = max(b, 1 + f(w))
        memo[v] = b; return b
    return max(f(v) for v in range(1, N+1))
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1
    K = {
     'i': lambda v: [((2*v-2) % N)+1, ((2*v-1) % N)+1],
     'ii': lambda v: [2*v, 2*v+1] if 2*v < M else [2*v-M, 2*v-M-1],
     'iii': lambda v: [2*v-1, 2*v] if 2*v <= M else [2*v-M, 2*v-M+1],
     'iv': lambda v: [2*v, 2*v+1, 2*v-M, 2*v-M-1],
     'v': lambda v: [2*v-1, 2*v, 2*v+1, 2*v-M-1, 2*v-M, 2*v-M+1],
    }
    res = {k: 99 for k in K}
    for a in A:
        tau = {m: i for i, m in enumerate(a)}
        for k, kd in K.items(): res[k] = min(res[k], longest(N, tau, kd))
    print(N, lg(M), res, flush=True)
