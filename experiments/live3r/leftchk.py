# leftchk.py: for the LEFT triples of rcall.txt, find a DFS prefix of valid steps after which
# the background satisfies Theorem G (pfx.c), so the triple is co-reachable (numerically).
import subprocess
for line in open('rcall.txt'):
    f = line.split()
    if len(f) < 5 or f[4] != 'LEFT':
        continue
    N = f[0]; res = None
    for o in ['1', str((int(N) + 1) // 2), N]:
        r = subprocess.run(['timeout', '120', './pfx', N, o] + f[1:4], capture_output=True, text=True).stdout.strip()
        if r and not r.startswith('FAIL'):
            res = r; break
    print(' '.join(f[:4]), res if res else 'UNKNOWN')
