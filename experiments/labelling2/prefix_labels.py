"""For admissible labellings: number of distinct labels in the prefix [1,s] (and suffix of
length s), compared with lg(s+1).  Prints, per N and s, the minimum over labellings, flagging
s where the minimum is < lg(s+1).  Also max label on suffix vs min label on prefix.
usage: prefix_labels.py file..."""
import sys, math
from collections import defaultdict
res = defaultdict(lambda: 99)
for fn in sys.argv[1:]:
    for line in open(fn):
        s = line.strip()
        if not s[:1].isdigit(): continue
        c = list(map(int, s)); N = len(c)
        for k in range(1, N + 1):
            res[N, k, 'pre'] = min(res[N, k, 'pre'], len(set(c[:k])))
            res[N, k, 'suf'] = min(res[N, k, 'suf'], len(set(c[N - k:])))
Ns = sorted(set(k[0] for k in res))
for N in Ns:
    bad_pre = [k for k in range(1, N + 1) if res[N, k, 'pre'] < int(math.log2(k + 1))]
    bad_suf = [k for k in range(1, N + 1) if res[N, k, 'suf'] < int(math.log2(k + 1))]
    print(f'N={N}: prefix fails at s={bad_pre[:8]}{"..." if len(bad_pre) > 8 else ""}  suffix fails at s={bad_suf[:8]}')
