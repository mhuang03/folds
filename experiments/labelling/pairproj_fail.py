"""Where does the first-occurrence pair projection fail to be right-heavy?
Prints, per file, a histogram of (y relative position, excess l - r) for failing steps."""
import glob, sys, collections
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    Np = (N - 1) // 2
    H = collections.Counter(); ex = []
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        a = sorted(range(1, N + 1), key=lambda m: (c[m], m))
        d = []; got = set()
        for m in a:
            y = m // 2
            if 1 <= y <= Np and y not in got:
                got.add(y); d.append(y)
        placed = set()
        for y in d:
            r = min(y - 1, Np - y)
            l = sum(1 for k in range(1, r + 1) if y - k in placed)
            rr = sum(1 for k in range(1, r + 1) if y + k in placed)
            if l > rr:
                side = 'L' if 2 * y <= Np + 1 else 'R'
                H[side, y, Np - y + 1, l - rr] += 1
                if len(ex) < 3: ex.append((s, y, l - rr))
            placed.add(y)
    print(N, t, Np, sorted(H.items())[:20], ex)
