"""For each admissible labelling (order a_c by (label, position)), the longest decreasing
subsequence starting at a given panel p (p first, then smaller panels with larger labels).
Reports, per N, the minimum over labellings of chain(p) for p = N, and max_p chain(p).
usage: chain_from.py DIR t Nmin Nmax"""
import sys, math
D, t, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
for N in range(a, b + 1):
    try: L = [l.strip() for l in open(f'{D}/all_{N}_{t}.txt') if l.strip()[:1].isdigit()]
    except FileNotFoundError: continue
    mins = None; minbest = None
    for s in L:
        c = list(map(int, s))
        # f[x] = longest chain starting at x: x, then y < x with c(y) > c(x), ...
        f = [1] * N
        for x in range(N):
            f[x] = 1 + max([f[y] for y in range(x) if c[y] > c[x]], default=0)
        prof = tuple(f)
        mins = f[N - 1] if mins is None else min(mins, f[N - 1])
        minbest = max(f) if minbest is None else min(minbest, max(f))
    print(f'N={N} t={t} lg(N+1)={int(math.log2(N+1))}: min chain from N = {mins}, min LDS = {minbest}')
