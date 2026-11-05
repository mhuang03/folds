"""Is the restriction of an admissible labelling to the left part [1..n] or the right part
[N-n+1..N] (n = (N-1)//2) admissible, and does it miss a label?"""
import glob
from reduce_test import adm
for f in sorted(glob.glob('all_*_*.txt'), key=lambda f: tuple(map(int, f[4:-4].split('_')))[::-1]):
    N, t = map(int, f[4:-4].split('_'))
    L = [l.strip() for l in open(f) if l.strip()]
    n = (N - 1) // 2
    st = dict(left=0, right=0, either=0, leftmiss=0, rightmiss=0)
    for s in L:
        c = [int(ch) for ch in s]
        lo = [0] + c[:n]; ro = [0] + c[N - n:]
        a = adm(lo); b = adm(ro)
        st['left'] += a; st['right'] += b; st['either'] += a or b
        st['leftmiss'] += a and len(set(lo[1:])) < t
        st['rightmiss'] += b and len(set(ro[1:])) < t
    print(N, t, len(L), st)
