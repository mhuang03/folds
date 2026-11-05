"""Suffix chain claim: reading the labels from the right end (gap 1, 2, ...), the first n labels
contain a strictly increasing subsequence of length >= lg(n+1), for every n <= N.
(A strictly increasing run of labels with decreasing positions is a decreasing subsequence of
the (label, position) order.)  Reports violations (N, t, labelling, n, lis)."""
import glob, sys, bisect
NMAX = eval(sys.argv.pop(1)) if len(sys.argv) > 1 and sys.argv[1].startswith("lambda") else (lambda N: N)
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
def lis_prefixes(seq):
    tails = []; out = []
    for v in seq:
        i = bisect.bisect_left(tails, v)
        if i == len(tails): tails.append(v)
        else: tails[i] = v
        out.append(len(tails))
    return out
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    bad = 0; ex = None; badn = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        seq = [int(ch) for ch in reversed(s)]
        L = lis_prefixes(seq)
        for n in range(1, NMAX(N) + 1):
            if L[n - 1] < (n + 1).bit_length() - 1:
                bad += 1; badn[n] = badn.get(n, 0) + 1
                if ex is None: ex = (s, n)
                break
    print(N, t, 'bad', bad, ex, sorted(badn.items()))
