"""Profiles of admissible labellings: a_v = #{x in P : c x < v}, P = [1, floor((N+1)/2)],
b_w = #{x in Q : c x >= t - w}, Q = the rest.  Report the maxima of a_v, b_w, a_v + b_w."""
import glob, collections
mx = collections.defaultdict(int)
arg = {}
for f in sorted(glob.glob('all_*_*.txt'), key=lambda f: tuple(map(int, f[4:-4].split('_')))[::-1]):
    N, t = map(int, f[4:-4].split('_'))
    h = (N + 1) // 2
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        a = [sum(1 for x in range(1, h + 1) if c[x] < v) for v in range(t + 1)]
        b = [sum(1 for x in range(h + 1, N + 1) if c[x] >= t - w) for w in range(t + 1)]
        for v in range(t + 1):
            for w in range(t + 1):
                k = (v, w)
                if a[v] + b[w] > mx[k]:
                    mx[k] = a[v] + b[w]; arg[k] = (N, t, s)
            if a[v] > mx['a', v]: mx['a', v] = a[v]; arg['a', v] = (N, t, s)
            if b[v] > mx['b', v]: mx['b', v] = b[v]; arg['b', v] = (N, t, s)
for k in sorted(mx, key=str):
    print(k, mx[k], arg.get(k))
