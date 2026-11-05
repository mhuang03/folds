"""Claim C ("natural intervals").  I = [a, b] is natural of width j if all labels on I lie in
[al, al + j), and (a = 1 or c(a-1) >= al + j) and (b = N or c(b+1) < al).
Claim: |I| <= 2^(j+1) - 2.  Also tests the variants with only one wall condition."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
worst = {}
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [int(ch) for ch in s]
        for a in range(N):
            lo = hi = c[a]
            for b in range(a, N):
                lo = min(lo, c[b]); hi = max(hi, c[b])
                L = b - a + 1
                for al in range(hi - (t - 1), lo + 1):   # al <= lo, al + j > hi
                    pass
                # minimal width containing labels: al = lo, j = hi - lo + 1 is the tightest;
                # walls: left must be >= al + j for some al <= lo, j >= hi - lo + 1 ...
                # take the choice maximising the chance: al = lo (needs right wall < lo),
                # j = hi - lo + 1 (needs left wall >= hi + 1)
                leftok = a == 0 or c[a - 1] > hi
                rightok = b == N - 1 or c[b + 1] < lo
                j = hi - lo + 1
                for typ, ok in (('both', leftok and rightok), ('left', leftok), ('right', rightok)):
                    if ok and L > 2 ** (j + 1) - 2:
                        key = (typ, j)
                        if L - (2 ** (j + 1) - 2) > worst.get(key, (0,))[0]:
                            worst[key] = (L - (2 ** (j + 1) - 2), N, s, a + 1, b + 1)
for k in sorted(worst): print(k, worst[k])
print('done')
