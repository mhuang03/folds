"""clone.py FILE COL NMIN NMAX : map of min width (digit, '-' if negative) of one column of clwidth."""
import sys
col, nmin, nmax = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mw = {}
for line in open(sys.argv[1]):
    a = line.split()
    N, r, d = int(a[0]), int(a[1]), int(a[2])
    if nmin <= N <= nmax:
        w = float(a[4 + col])
        mw[(r, d)] = min(w, mw.get((r, d), 99))
rs = sorted(set(r for r, d in mw))
ds = sorted(set(d for r, d in mw))
print('     ' + ''.join(str(d // 10) for d in ds))
print('     ' + ''.join(str(d % 10) for d in ds))
for r in rs:
    print('%4d ' % r + ''.join((' ' if (r, d) not in mw else ('-' if mw[(r, d)] < 0 else str(min(9, int(mw[(r, d)] * 10)))))
                               for d in ds))
