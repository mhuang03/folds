"""Claim C: for every panel m of an admissible labelling, with W(m) = [m-r, m+r],
   2r+1 <= 2^(k+1) - 2,   k = max - min + 1 of the labels on W(m)  (also: k = #distinct).
Also tests the same for every sub-interval of the form [m-r', m+r'] with r' <= r(m)."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    bad_span = bad_dist = bad_sub = 0; ex = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        for m in range(1, N + 1):
            r = min(m - 1, N - m)
            W = c[m - r:m + r + 1]
            k1 = max(W) - min(W) + 1; k2 = len(set(W))
            if 2 * r + 1 > 2 ** (k1 + 1) - 2:
                bad_span += 1; ex.setdefault('span', (s, m))
            if 2 * r + 1 > 2 ** (k2 + 1) - 2:
                bad_dist += 1; ex.setdefault('dist', (s, m))
            for rr in range(r):
                W = c[m - rr:m + rr + 1]
                if 2 * rr + 1 > 2 ** (max(W) - min(W) + 2) - 2:
                    bad_sub += 1; ex.setdefault('sub', (s, m, rr)); break
    print(N, t, bad_span, bad_dist, bad_sub, ex)
