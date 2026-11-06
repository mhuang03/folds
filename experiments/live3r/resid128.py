# resid.py N1 N2 [maxd]: the residual triples (no transfer, no Theorem G after <= maxd steps,
# for the triple or its mirror image), canonical orientation a + c <= N + 1, from ./hints
import subprocess, sys
maxd = sys.argv[3] if len(sys.argv) > 3 else '2'
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    out = subprocess.run(['./hints128', str(N), maxd], capture_output=True, text=True).stdout
    S = set()
    for line in out.split('\n'):
        f = line.split()
        if len(f) > 4 and f[4] in ('W', 'FAIL'):
            a, b, c = map(int, f[:3])
            if a + c > N + 1: a, b, c = N + 1 - c, N + 1 - b, N + 1 - a
            S.add((a, b, c))
    print('N=%d residual=%d: %s' % (N, len(S), ' '.join('(%d,%d,%d)' % t for t in sorted(S))))
    sys.stdout.flush()
