"""Which residue classes C_s = {s, s+q, ...} of [N] satisfy Theorem G' (peel.py), i.e. have a
complement reachable by the greedy?  In particular the exceptional classes (s = 1 with
N = 1 mod q, s = q with N = -1 mod q, q not a power of 2)."""
import sys
from peel import peel

NMAX = int(sys.argv[1])
exc_ok = exc_tot = 0
for N in range(4, NMAX + 1):
    for q in range(2, N):
        for s in range(1, q + 1):
            C = set(range(s, N + 1, q))
            exc = (q & (q - 1)) != 0 and ((N % q == 1 and s == 1) or (N % q == q - 1 and s == q))
            if exc:
                exc_tot += 1
                if peel(N, C):
                    exc_ok += 1
                    print('exceptional class peels: N=%d q=%d s=%d' % (N, q, s))
print('exceptional classes satisfying G\':', exc_ok, 'of', exc_tot)
tot = ok = 0
for N in range(4, NMAX + 1):
    for q in range(2, N):
        for s in range(1, q + 1):
            tot += 1
            ok += peel(N, set(range(s, N + 1, q)))
print('all classes satisfying G\':', ok, 'of', tot)
