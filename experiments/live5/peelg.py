"""peelg.py: Theorem G' (signs + acyclic priorities) for a general background set B, by peeling
(see experiments/adjacent/peel.py): peel(N, B) is True iff the criterion holds."""
from lib import imb


def peel(N, B):
    B = set(B)
    W = set(range(1, N + 1)) - B
    I, arm = {}, {}
    for m in W:
        r = min(m - 1, N - m)
        I[m] = imb(N, B, m)
        arm[m] = (range(m - r, m), range(m + 1, m + r + 1))
    changed = True
    while W and changed:
        changed = False
        for m in sorted(W):
            L, R = arm[m]
            if (I[m] <= 0 and not any(x in W for x in L)) or \
               (I[m] >= 0 and not any(x in W for x in R)):
                W.discard(m)
                changed = True
    return not W
