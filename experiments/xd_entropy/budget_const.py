#!/usr/bin/env python3
"""budget_const.py -- constants of the budget bound (Lean: XdEntropy.semiCount_le_budget).

caps u_k  : the per-state bounds of Folds/MaxMoves2.lean (2-adic bound with the size term;
            parity bound at odd levels), u_k <= N-k.
budget    : 2 sum_k (u_k - c)^+ + 2 sum_k (N-k-u_k) <= E(N)   ==>   a(N) <= prod_k min(u_k, c).
Prints, per N: saving/N := (ln N! - ln bound)/N for
   caps only | kick only (u_k = N-k) | caps + kick budget.
"""
import math, sys

def E(N):
    # mutually visible pairs x<y: y-x <= min(reach x, reach y)
    tot = 0
    for x in range(1, N + 1):
        rx = min(x - 1, N - x)
        for d in range(1, rx + 1):
            y = x + d
            if y > N: break
            if d <= min(y - 1, N - y): tot += 1
    return tot

def v2(k):
    a = 0
    while k % 2 == 0: k //= 2; a += 1
    return a

def caps(N):
    u = []
    for k in range(N):
        f = N - k
        if k == 0: u.append(f)
        elif k % 2 == 1:
            u.append(min(f, N // 2) if N % 2 == 0 else min(f, N // 2 + 1 + k // 2))
        else:
            a = v2(k)
            u.append(min(f, (2 * (a + 1) * N + a - 2 * (a - 1) * k) // (2 * (a + 2))))
    return u

def best_c(N, u, e):
    forced = 2 * sum((N - k) - u[k] for k in range(N))
    if forced > e: return None      # budget already implied by the caps
    lo, hi = 1, N                   # smallest c with 2 sum (u_k-c)^+ <= e - forced
    while lo < hi:
        mid = (lo + hi) // 2
        if 2 * sum(max(0, x - mid) for x in u) <= e - forced: hi = mid
        else: lo = mid + 1
    return lo

def saving(N, u, c):
    return (math.lgamma(N + 1) - sum(math.log(min(x, c)) for x in u)) / N

if __name__ == "__main__":
    Ns = [int(x) for x in sys.argv[1:]] or [64, 65, 256, 257, 1024, 1025, 4096, 4097]
    print("    N   E/N^2  2*forced/E  caps-only  kick-only  caps+kick (c/N)")
    for N in Ns:
        e = E(N); u = caps(N); free = [N - k for k in range(N)]
        forced = 2 * sum((N - k) - u[k] for k in range(N))
        c0 = best_c(N, free, e); c1 = best_c(N, u, e)
        s_caps = saving(N, u, N); s_kick = saving(N, free, c0)
        s_both = saving(N, u, c1) if c1 else s_caps
        print(f"{N:5d} {e/N/N:.5f}   {forced/e:.4f}     {s_caps:.4f}     {s_kick:.4f}     {s_both:.4f} "
              f"({(c1 or N)/N:.3f})")
