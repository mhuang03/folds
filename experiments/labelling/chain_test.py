"""Chains through a panel.  A chain is a sequence of panels with decreasing positions and
strictly increasing labels.  lam(m) = longest chain whose top (leftmost) element is m,
rho(m) = longest chain whose bottom (rightmost) element is m.  Test, for every panel m:
   (A)  lam(m) + rho(m) - 1 >= lg(r(m)+1) + 1
   (B)  the longest chain inside the window W(m) has length >= lg(r(m)+1) + 1
   (C)  the longest chain in [1,N] through some panel of W(m) ... (= global LDS, trivial)."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
lg = lambda n: n.bit_length() - 1
def longest_chain(lab):   # labels in position order; chain = decreasing positions, increasing labels
    best = [1] * len(lab)  # best[i] = longest chain with top at i (i leftmost)
    for i in range(len(lab) - 1, -1, -1):
        for j in range(i + 1, len(lab)):
            if lab[j] < lab[i]: best[i] = max(best[i], best[j] + 1)
    return best
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    badA = badB = 0; exA = exB = None
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [int(ch) for ch in s]
        lam = longest_chain(c)
        rho = longest_chain([-v for v in reversed(c)])[::-1]
        for i in range(N):
            m = i + 1; r = min(m - 1, N - m)
            need = lg(r + 1) + 1
            if lam[i] + rho[i] - 1 < need:
                badA += 1; exA = exA or (s, m)
            W = c[i - r:i + r + 1]
            if max(longest_chain(W)) < need:
                badB += 1; exB = exB or (s, m)
    print(N, t, 'A', badA, exA, 'B', badB, exB)
