"""beatty_B.py N1 N2: for every Beatty window copy X = X(N,p,g) (2p-1-N <= g <= 0), split the
complement Y = [N] \\ X by index parity, Y_A (even-indexed) and Y_B (odd-indexed).  Test the
two-block route  Y_A then Y_B  (or Y_B then Y_A): both copies and the first complete block
balanced around every point of the second.  Prints the X for which neither order works."""
import sys
from beatty_cover import copy_crit
from splits import balanced

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    bad = []
    tot = 0
    for p in range(1, N):
        seen = set()
        for g in range(2 * p - 1 - N, 1):
            X = tuple((r * N + g) // p for r in range(1, p + 1))
            if X in seen:
                continue
            seen.add(X)
            tot += 1
            Y = [y for y in range(1, N + 1) if y not in X]
            YA, YB = Y[1::2], Y[0::2]
            ok = False
            for A, B in ((YA, YB), (YB, YA)):
                if copy_crit(N, A) and copy_crit(N, B) and all(balanced(N, A, m) for m in B):
                    ok = True
            if not ok:
                bad.append((p, g, X))
    print(N, tot, len(bad), bad[:6])
