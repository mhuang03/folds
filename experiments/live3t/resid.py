# resid.py N0 N1 [K]: the residual of Covered3T (Folds/Live3s.lean) for N = N0..N1.
# Per N: the residual of Live3q's rules (bin/hints256 with NOWIT=1, canonical orientation
# a + c <= N + 1), then the Live3r rules (bin/rcov256, nearTrB with <= K steps for the image,
# nearTrP with YPSI=1, chiX), then the closed-form families OneTwo of Live3s.
# Writes bin/l<N>.txt (Live3q residual), bin/c<N>.txt (rcov hints); prints one line per N:
#   N=.. q=<Live3q residual> r=<left by Covered3R> T: <left by Covered3T, as a,b,c>
import subprocess, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'live3s'))
from base import onetwo
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bin')
N0, N1 = int(sys.argv[1]), int(sys.argv[2])
K = sys.argv[3] if len(sys.argv) > 3 else '4'
env = dict(os.environ, NOWIT='1', YPSI='1')
for N in range(N0, N1 + 1):
    out = subprocess.run([os.path.join(D, 'hints256'), str(N), '2'], capture_output=True,
                         text=True, env=env).stdout
    S = set()
    for line in out.split('\n'):
        f = line.split()
        if len(f) > 4 and f[4] in ('W', 'FAIL'):
            a, b, c = map(int, f[:3])
            if a + c > N + 1: a, b, c = N + 1 - c, N + 1 - b, N + 1 - a
            S.add((a, b, c))
    lf = os.path.join(D, 'l%d.txt' % N)
    open(lf, 'w').write(''.join('%d %d %d %d\n' % (N, *t) for t in sorted(S)))
    cov = subprocess.run([os.path.join(D, 'rcov256'), lf, K], capture_output=True, text=True,
                         env=env).stdout
    open(os.path.join(D, 'c%d.txt' % N), 'w').write(cov)
    left = [tuple(map(int, l.split()[1:4])) for l in cov.split('\n') if l.endswith('LEFT')]
    still = [t for t in left if not ((t[0], t[1]) == (1, 2) and onetwo(N, t[2]))]
    print('N=%d q=%d r=%d T: %s' % (N, len(S), len(left), ' '.join('%d,%d,%d' % t for t in still)))
    sys.stdout.flush()
