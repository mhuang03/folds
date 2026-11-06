"""zeroset.py N1 N2: the Zero-set Lemma on pairs.
If R lies in the zero set of I_D (I_D(m) = 0 for m in R), R is orderable from scratch and D + R
is co-reachable (here: inward, Theorem G), then D is co-reachable.
Tests R = one point, R = two points, for the non-inward non-dead pairs."""
import sys
from lib import imb


def inward_set(N, B):
    B = set(B)
    neg, pos = [], []
    for m in range(1, N + 1):
        if m in B:
            continue
        i = imb(N, B, m)
        if i < 0:
            neg.append(m)
        elif i > 0:
            pos.append(m)
    return not neg or not pos or max(neg) < min(pos)


def dead(N, u, v):
    return u == 1 and v == N and ((N % 2 == 0 and N >= 4) or N == 7)


def valid2(N, x, y):
    """[x, y] valid from scratch (y's window avoids x or balanced)."""
    return imb(N, {x}, y) == 0


if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        miss1, miss2 = [], []
        tot = 0
        for u in range(1, N + 1):
            for v in range(u + 1, N + 1):
                if dead(N, u, v) or inward_set(N, {u, v}):
                    continue
                if (N + 1 - v, N + 1 - u) < (u, v):
                    continue
                tot += 1
                D = {u, v}
                Z = [m for m in range(1, N + 1) if m not in D and imb(N, D, m) == 0]
                ok1 = any(inward_set(N, D | {x}) for x in Z)
                if not ok1:
                    miss1.append((u, v))
                    ok2 = any(inward_set(N, D | {x, y}) for x in Z for y in Z
                              if x != y and valid2(N, x, y))
                    if not ok2:
                        miss2.append((u, v))
        print(N, 'non-inward (up to mirror)', tot, 'one point fails', len(miss1),
              'two points fail', len(miss2), miss2[:12], flush=True)
