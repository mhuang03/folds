# imgdfs.py PFX N c [c ...]: for the moved near copies of moved.py (odd N, wrong parity c),
# run the DFS of ../live3r/pfx.c (binary PFX) on the image as background: a prefix of valid
# steps after which Theorem G holds, i.e. an ordering of the complement from scratch.
import subprocess, sys
from moved import maps_for
pfx, N = sys.argv[1], int(sys.argv[2])
for c in map(int, sys.argv[3:]):
    p, g, f = maps_for(N, c)
    img = sorted({f(y) for y in range(1, p + 1)})
    for o in ['1', str(c), str(N)]:
        r = subprocess.run(['timeout', '60', pfx, str(N), o] + list(map(str, img)),
                           capture_output=True, text=True).stdout.strip()
        if r and not r.startswith('FAIL'): break
    print(N, c, 'g=%d' % g, r)
