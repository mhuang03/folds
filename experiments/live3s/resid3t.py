# resid3t.py BIN N0 N1: the residual of Covered3T beyond Live3r's range.  BIN holds the binaries
# of ../live3r (hints128, rcov) and resid128.py / tolines.py; per N: the residual of Live3q's
# rules (hints128), then the Live3r rules (rcov, 4 steps), then the closed-form families
# OneTwo of Live3s.  Prints the triples still left (canonical orientation).
import subprocess, sys, os
from base import onetwo
B, N0, N1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
for N in range(N0, N1 + 1):
    r = subprocess.run(['python3', 'resid128.py', str(N), str(N), '2'], cwd=B,
                       capture_output=True, text=True).stdout
    open(os.path.join(B, 'r%d.txt' % N), 'w').write(r)
    lines = subprocess.run(['python3', 'tolines.py', 'r%d.txt' % N], cwd=B,
                           capture_output=True, text=True).stdout
    open(os.path.join(B, 'l%d.txt' % N), 'w').write(lines)
    cov = subprocess.run(['./rcov', 'l%d.txt' % N, '4'], cwd=B, capture_output=True,
                         text=True).stdout
    left = [tuple(map(int, l.split()[:4])) for l in cov.split('\n') if l.endswith('LEFT')]
    other = [t for t in left if (t[1], t[2]) != (1, 2)]
    still = [t[3] for t in left if (t[1], t[2]) == (1, 2) and not onetwo(N, t[3])]
    print('N=%d: Live3q residual %d, left by Covered3R %d (not {1,2,c}: %s), left by Covered3T: '
          '{1,2,c} c in %s' % (N, len(lines.split('\n')) - 1, len(left), other, still))
    sys.stdout.flush()
