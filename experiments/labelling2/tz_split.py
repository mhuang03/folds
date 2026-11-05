"""Split [N] by the bottom class Z (labels 0) and top class T (labels t-1):
L_Z = [1, min Z) (labels >= 1, touches the left edge), R_T = (max T, N] (labels <= t-2, touches
the right edge), middle = the rest.  Report max |L_Z|, |R_T|, and the middle size, per (t, N),
for labellings that use all t labels.
usage: tz_split.py t file..."""
import sys
from collections import defaultdict
t = int(sys.argv[1])
st = defaultdict(lambda: [0, 0, -99, 99, None])
for fn in sys.argv[2:]:
    for line in open(fn):
        s = line.strip()
        if not s[:1].isdigit(): continue
        c = list(map(int, s)); N = len(c)
        if len(set(c)) < t: continue
        mz = min(i for i in range(N) if c[i] == 0) + 1
        mt = max(i for i in range(N) if c[i] == t - 1) + 1
        LZ = mz - 1; RT = N - mt; mid = N - LZ - RT
        a = st[N]
        a[0] = max(a[0], LZ); a[1] = max(a[1], RT)
        if mid > a[2]: a[2] = mid; a[4] = s
        a[3] = min(a[3], mid)
for N in sorted(st):
    a = st[N]
    print(f't={t} N={N}: max|L_Z|={a[0]} max|R_T|={a[1]} (2^t-2={2**t-2}) middle in [{a[3]},{a[2]}] e.g. {a[4]}')
