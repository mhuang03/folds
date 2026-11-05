"""Stage lemma candidates.  S_v = {c < v} (placed after v phases), remaining phases t - v
(t = max label + 1).  For an unplaced m (c(m) >= v) with r = r(m):
  (F1) if R(m) is entirely unplaced, then t - v >= lg(r+1) + 1;
  (F2) if W(m) is entirely unplaced, then t - v >= lg(r+1) + 1;
  (F3) if |S n R(m)| <= |S n L(m)| ..."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
lg = lambda n: n.bit_length() - 1
for f in files:
    N, t0 = map(int, f.split('/')[-1][4:-4].split('_'))
    bad = {'F1': 0, 'F2': 0, 'F3': 0}; ex = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        t = max(c[1:]) + 1
        for m in range(1, N + 1):
            r = min(m - 1, N - m)
            for v in range(0, c[m] + 1):
                need = lg(r + 1) + 1
                Rp = sum(1 for d in range(1, r + 1) if c[m + d] < v)
                Lp = sum(1 for d in range(1, r + 1) if c[m - d] < v)
                if Rp == 0 and t - v < need:
                    bad['F1'] += 1; ex.setdefault('F1', (s, m, v))
                if Rp == 0 and Lp == 0 and t - v < need:
                    bad['F2'] += 1; ex.setdefault('F2', (s, m, v))
                if Rp <= Lp and t - v < need:
                    bad['F3'] += 1; ex.setdefault('F3', (s, m, v))
    print(N, t0, bad, ex)
