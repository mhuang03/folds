"""prefG.py N maxlen D...: shortest background prefixes after which the remaining set is inward
(Theorem G applies to D + prefix).  BFS over sets (prefix sets), prints a few minimal ones."""
import sys
from lib import imb
from zeroset import inward_set
from peelg import peel
if "-p" in sys.argv:
    sys.argv.remove("-p")
    inward_set = peel

N = int(sys.argv[1])
maxlen = int(sys.argv[2])
D = frozenset(int(x) for x in sys.argv[3:])
show = 6
frontier = {D: []}
for L in range(maxlen + 1):
    found = [(sorted(S - D), p) for S, p in frontier.items() if inward_set(N, S)]
    if found:
        print('length', L, 'count', len(found))
        for s, p in found[:show]:
            print('  set', s, 'order', p)
        break
    nf = {}
    for S, p in frontier.items():
        for x in range(1, N + 1):
            if x not in S and imb(N, S, x) == 0:
                T = S | {x}
                if T not in nf:
                    nf[T] = p + [x]
    frontier = nf
    print('level', L + 1, len(frontier), flush=True)
