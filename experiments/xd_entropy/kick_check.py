#!/usr/bin/env python3
"""kick_check.py -- the kick budget and the resulting upper bound.

For a valid sequence a_1..a_N, S_k = {a_1..a_k}, V_k = #valid moves at S_k,
bad_k = (N-k) - V_k.  For 1 <= k <= N-1 let c_k = #{m not in S_k : a_k in W_m}.
Checks (exhaustively over all valid sequences, N <= NMAX):
  (K1) bad_{k-1} + bad_k >= c_k                     (window parity flips at each kick)
  (K2) sum_k c_k >= E(N) = #{x<y : y-x <= min(reach x, reach y)}   (mutually visible pairs)
  (K3) prod_k V_k <= c! c^(N-c) whenever (N-c)(N-c+1) <= E(N)
and prints E(N), the best c, and the constants for large N.
usage: kick_check.py [NMAX=9]
"""
import sys, math

def reach(N, m): return min(m - 1, N - m)

def E(N):
    return sum(1 for x in range(1, N + 1) for y in range(x + 1, N + 1)
               if y - x <= reach(N, x) and y - x <= reach(N, y))

def best_c(N):
    e = E(N)
    c = N
    while c > 1 and (N - (c - 1)) * (N - (c - 1) + 1) <= e:
        c -= 1
    return c

def lnbound(N, c):  # ln( c! c^(N-c) )
    return math.lgamma(c + 1) + (N - c) * math.log(c)

def valid_moves(N, S):
    out = []
    for m in range(1, N + 1):
        if m in S: continue
        r = reach(N, m)
        if sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S):
            out.append(m)
    return out

def check(N):
    e = E(N); c = best_c(N); B = math.factorial(c) * c ** (N - c)
    cnt = 0; worst = (10**9, None); maxprod = 0; minC = 10**9; minbad = 10**9
    seq = []; S = set(); Vs = []
    def rec():
        nonlocal cnt, maxprod, minC, minbad
        k = len(seq)
        mv = valid_moves(N, S)
        if k == N:
            cnt += 1
            bad = [N - i - Vs[i] for i in range(N)]
            Ssofar = set(); Csum = 0
            for kk in range(1, N):
                x = seq[kk - 1]; Ssofar.add(x)
                ck = sum(1 for m in range(1, N + 1) if m not in Ssofar and abs(m - x) <= reach(N, m))
                assert bad[kk - 1] + bad[kk] >= ck, (seq, kk)
                Csum += ck
            assert Csum >= e, (seq, Csum, e)
            p = math.prod(Vs)
            assert p <= B, (seq, p, B)
            maxprod = max(maxprod, p); minC = min(minC, Csum); minbad = min(minbad, sum(bad))
            return
        Vs.append(len(mv))
        for m in mv:
            seq.append(m); S.add(m)
            rec()
            seq.pop(); S.discard(m)
        Vs.pop()
    rec()
    print(f"N={N:2d} a(N)={cnt} E={e} best c={c} bound c!c^(N-c)={B} max prodV={maxprod} "
          f"min sum c_k={minC} min sum bad={minbad} (E/2={e/2})")

if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    for N in range(1, NMAX + 1):
        check(N)
    print("\nlarge N: E(N)/N^2, c/N, saving = (ln N! - ln(c! c^(N-c)))/N")
    for N in [16, 17, 32, 33, 64, 65, 128, 129, 256, 257, 1024, 1025]:
        e = E(N); c = best_c(N)
        print(f"N={N:5d} E/N^2={e/N/N:.5f} c/N={c/N:.4f} saving/N={(math.lgamma(N+1)-lnbound(N,c))/N:.4f}")
    x = 1 - 1 / math.sqrt(6)
    print(f"limit: E/N^2 -> 1/6, c/N -> 1-1/sqrt(6) = {x:.5f}, saving/N -> -ln(c)-1+c = {-math.log(x)-1+x:.5f}")
