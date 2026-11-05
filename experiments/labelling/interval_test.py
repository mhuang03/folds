"""Claim B: in an admissible labelling every interval of panels all with labels < j has length
<= 2^(j+1) - 2.  Reports, per file, the max interval length for each j and violations."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    mx = [0] * (t + 1); arg = [None] * (t + 1)
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [int(ch) for ch in s]
        for j in range(1, t + 1):
            run = best = 0
            for v in c:
                run = run + 1 if v < j else 0
                best = max(best, run)
            if best > mx[j]: mx[j] = best; arg[j] = s
    viol = [j for j in range(1, t + 1) if mx[j] > 2 ** (j + 1) - 2]
    print(N, t, 'max run per j', mx[1:], 'violations', [(j, arg[j]) for j in viol])
