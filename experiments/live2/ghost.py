"""ghost.py N1 N2: mixed 2-sets D = {o, e} (o odd, e even).  Is [N] \\ D reachable by
  P1: all of O - {o} first (in any valid order of the odd strip), then E - {e}, or
  P2: E - {e} first, then O - {o}?
The second block sees the first as its full class minus one point (a 'ghost' hole).  The
second-block feasibility is decided by a subset DP inside that class.  Prints failures."""
import sys
from lib import arms


def second_block_ok(N, C, hole, miss, first):
    """Can C - {miss} be ordered on background first = (other class - {hole})?"""
    T = [x for x in C if x != miss]
    idx = {x: i for i, x in enumerate(T)}
    nT = len(T)
    A = [arms(N, x) for x in T]
    base = [len(L & first) - len(R & first) for (L, R) in A]
    Lm = [sum(1 << idx[z] for z in L if z in idx) for (L, R) in A]
    Rm = [sum(1 << idx[z] for z in R if z in idx) for (L, R) in A]
    reach = bytearray(1 << nT)
    reach[0] = 1
    for S in range(1 << nT):
        if not reach[S]:
            continue
        for i in range(nT):
            if not S >> i & 1:
                if base[i] + bin(S & Lm[i]).count('1') - bin(S & Rm[i]).count('1') == 0:
                    reach[S | 1 << i] = 1
    return bool(reach[(1 << nT) - 1])


def options(N, o, e):
    O = [x for x in range(1, N + 1, 2)]
    E = [x for x in range(2, N + 1, 2)]
    p1 = second_block_ok(N, E, o, e, set(O) - {o})
    p2 = second_block_ok(N, O, e, o, set(E) - {e})
    return p1, p2


if __name__ == '__main__':
    adj_only = 'adj' in sys.argv[3:]
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        fails = []
        for o in range(1, N + 1, 2):
            for e in range(2, N + 1, 2):
                if adj_only and abs(o - e) != 1:
                    continue
                p1, p2 = options(N, o, e)
                if not (p1 or p2):
                    fails.append((min(o, e), max(o, e)))
        print(N, len(fails), sorted(fails))
        sys.stdout.flush()
