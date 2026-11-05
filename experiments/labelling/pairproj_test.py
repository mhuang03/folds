"""Pair projection on right-heavy permutations.  From an admissible labelling c, a = panels
sorted by (c, position) (a right-heavy permutation with <= t runs).  Project the pairs
{2y, 2y+1}, y = 1..N' = (N-1)//2, by first (or last) occurrence, giving a permutation d of
[N'].  Test: is d right-heavy?  LDS(d) <= LDS(a) - 1?  runs(d) <= runs(a) - 1?"""
import glob, sys, bisect
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
def right_heavy(seq, N):
    placed = set()
    for m in seq:
        r = min(m - 1, N - m)
        l = sum(1 for d in range(1, r + 1) if m - d in placed)
        rr = sum(1 for d in range(1, r + 1) if m + d in placed)
        if l > rr: return False
        placed.add(m)
    return True
def lds(seq):
    tails = []
    for v in seq:
        v = -v
        i = bisect.bisect_left(tails, v)
        if i == len(tails): tails.append(v)
        else: tails[i] = v
    return len(tails)
def runs(seq):
    return 1 + sum(1 for i in range(len(seq) - 1) if seq[i + 1] < seq[i])
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    Np = (N - 1) // 2
    st = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        a = sorted(range(1, N + 1), key=lambda m: (c[m], m))
        for mode in ('first', 'last'):
            seen = []; got = set()
            it = a if mode == 'first' else a[::-1]
            for m in it:
                y = m // 2
                if 1 <= y <= Np and y not in got:
                    got.add(y); seen.append(y)
            d = seen if mode == 'first' else seen[::-1]
            k = (mode,)
            rh = right_heavy(d, Np)
            st[k + ('rh',)] = st.get(k + ('rh',), 0) + rh
            st[k + ('lds',)] = st.get(k + ('lds',), 0) + (lds(d) <= lds(a) - 1)
            st[k + ('runs',)] = st.get(k + ('runs',), 0) + (runs(d) <= runs(a) - 1)
        st['n'] = st.get('n', 0) + 1
    print(N, t, st)
