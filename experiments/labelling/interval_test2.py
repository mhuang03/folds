"""Max length of an interval of panels all with label < j, by type:
inner (touches no edge), right (contains panel N, not 1), left (contains panel 1, not N)."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
best = {}
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [int(ch) for ch in s]
        for j in range(1, t):
            i = 0
            while i < N:
                if c[i] >= j: i += 1; continue
                k = i
                while k < N and c[k] < j: k += 1
                typ = ('left' if i == 0 else '') + ('right' if k == N else '') or 'inner'
                key = (j, typ)
                if k - i > best.get(key, (0,))[0]: best[key] = (k - i, N, t, s)
                i = k
for k in sorted(best): print(k, best[k])
