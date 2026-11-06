# left12.py: (1) which of the 86 triples {1, 2, c} left by Live3r (N = 51..70,
# ../live3r/leftchk.txt) are settled by the closed-form families OneTwo of Live3s;
# (2) for N0..N1, the c with {1, 2, c} valid, not dead and not in OneTwo (whether or not some
# other rule of Covered3R settles them).
import sys
from base import cs12, onetwo

left86 = []
for line in open('../live3r/leftchk.txt'):
    f = line.split()
    left86.append((int(f[0]), int(f[1]), int(f[2]), int(f[3])))
now = [t for t in left86 if not (t[1] == 1 and t[2] == 2 and onetwo(t[0], t[3]))]
print('Live3r left %d triples; settled now by OneTwo: %d; still left: %d' %
      (len(left86), len(left86) - len(now), len(now)))
byN = {}
for (N, a, b, c) in now: byN.setdefault(N, []).append(c if (a, b) == (1, 2) else (a, b, c))
for N in sorted(byN): print('  N=%d: %s' % (N, byN[N]))
if len(sys.argv) > 2:
    print('{1,2,c} not in OneTwo (c >= 8):')
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        print('  N=%d (mod 8 = %d): %s' % (N, N % 8, [c for c in cs12(N) if c >= 8 and not onetwo(N, c)]))
