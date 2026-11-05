"""Where can a longest chain (decreasing positions, strictly increasing labels) start / end?
For each labelling: L = lg(N+1); report how often there is a chain of length >= L
  (a) starting at panel N (its lowest-label, rightmost element is N),
  (b) ending at panel 1, (c) through the middle panel(s), (d) at all."""
import glob, sys
from chain_test import longest_chain
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
lg = lambda n: n.bit_length() - 1
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    L = lg(N + 1); st = dict(n=0, startN=0, end1=0, mid=0, any=0)
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [int(ch) for ch in s]
        lam = longest_chain(c)                                   # top = leftmost element
        rho = longest_chain([-v for v in reversed(c)])[::-1]     # bottom = rightmost element
        st['n'] += 1
        st['startN'] += rho[N - 1] >= L
        st['end1'] += lam[0] >= L
        mids = [(N - 1) // 2, N // 2]
        st['mid'] += any(lam[i] + rho[i] - 1 >= L for i in mids)
        st['any'] += max(lam) >= L
    print(N, t, L, st)
