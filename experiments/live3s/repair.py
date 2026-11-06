# repair.py N0 N1: for the moved near copies of moved.py, try explicit step patterns for the image
# (the base step 4 or 5, then a repair of the hole next to c) and report which pattern makes
# the background satisfy Theorem G with the centre 1/2 (inward1) or any centre.
import sys
from base import *
from moved import maps_for, regular_except

def run(N, B, steps):
    B = set(B)
    for m in steps:
        if not valid(N, B, m): return None
        B.add(m)
    return B

if __name__ == '__main__':
    N0, N1 = int(sys.argv[1]), int(sys.argv[2])
    for N in range(N0, N1 + 1):
        if N % 2 == 0: continue
        s0 = 4 if N % 4 == 1 else 5
        out = []
        for c in range(6, N - 1):
            r = maps_for(N, c)
            if r is None: continue
            p, g, f = r
            if not (3 <= g <= p - 2): continue
            if regular_except(N, p, f, {1, 2, g}): out.append((c, 'IRR')); continue
            img = {f(y) for y in range(1, p + 1)}
            pats = [[s0], [s0, c - 2, c - 1], [s0, c + 2, c + 1], [c - 2, c - 1, s0], [c + 2, c + 1, s0]]
            found = None
            for k, pat in enumerate(pats):
                B = run(N, img, pat)
                if B is not None and inward1(N, B): found = (k, 'c1'); break
            if found is None:
                for k, pat in enumerate(pats):
                    B = run(N, img, pat)
                    if B is not None and centre(N, B): found = (k, 'any'); break
            out.append((c, found))
        print(N, N % 8, ' '.join('%d:%s' % (c, '-' if x is None else (x if isinstance(x, str) else '%d%s' % (x[0], x[1][0]))) for c, x in out))
