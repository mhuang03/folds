"""Max length of an edge-anchored window [M-2g+1, N] (right edge) whose labels span k values,
and of left-edge windows [1, 2x-1], over all enumerated admissible labellings."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
R = {}; L = {}
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [int(ch) for ch in s]
        for g in range(1, (N + 1) // 2 + 1):
            W = c[N - (2 * g - 1):]
            k = max(W) - min(W) + 1
            if 2 * g - 1 > R.get(k, (0,))[0]: R[k] = (2 * g - 1, N, s)
            W = c[:2 * g - 1]
            k = max(W) - min(W) + 1
            if 2 * g - 1 > L.get(k, (0,))[0]: L[k] = (2 * g - 1, N, s)
print('right edge', sorted(R.items()))
print('left edge', sorted(L.items()))
