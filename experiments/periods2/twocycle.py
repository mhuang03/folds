"""twocycle.py S1 S2 F [samples]: can two DISJOINT halving cycles (periods S1, S2 of the doubling
map) occur in one face?  A face whose tight system has two (U) components with s = S1, S2 (and
nothing else) is: S1 + 1 points at a periodic orbit vertex (x = theta_A, backwards orbit,
closing equality), S2 + 1 points likewise for theta_B, interleaved in time arbitrarily, plus F
free points (codimension m = S1 + S2 + 2, K = m + F).  It is a face of some class polytope iff
some local cell is valid: every free column sums to 0 and every cycle column has a valid side
(PROOFS.txt section 2).  We enumerate theta_A, theta_B (exact periods, no coincidences or
accidental tight relations between the two cycles), all interleavings, all time placements of
the free points, and free values: exact interval midpoints for F = 1, random samples for F >= 2.
Prints the number of valid configurations and examples."""
import sys
import random
from fractions import Fraction as Fr
from itertools import combinations
from face import sgn, breakpoints


def orbit_points(s):
    D = 2 ** s - 1
    out = []
    for a in range(1, D):
        x = Fr(a, D)
        orb = [x]
        for _ in range(s):
            orb.append((2 * orb[-1]) % 1)
        if len(set(orb[:-1])) == s:
            v = [orb[s + 1 - j] for j in range(1, s + 2)]   # x_1 = theta, ..., x_{s+1} = theta
            bits = [int(2 * v[t] - v[t - 1]) for t in range(1, s + 1)]
            out.append((v, bits))
    return out


def accidental(vA, vB):
    for x in set(vA):
        for y in set(vB):
            if x == y or 2 * x - y in (0, 1) or 2 * y - x in (0, 1):
                return True
    return False


def check(seq, cycles):
    """cycles: list of (positions in cycle order, bits).  True iff a valid cell exists."""
    tight = set()
    role = {}
    for pos, bits in cycles:
        M = len(pos)
        for t in range(1, M):
            tight.add((pos[t - 1], pos[t]))
            role[pos[t]] = (bits[t - 1], t == M - 1)
        tight.add((pos[0], pos[-1]))
    for j in range(len(seq)):
        s = sum(sgn(seq[i], seq[j]) for i in range(j) if (i, j) not in tight)
        if j not in role:
            if s != 0:
                return False
            continue
        cb, last = role[j]
        sigs = (1, 0) if cb == 1 else (0, -1)
        if not last:
            if not any(s + g == 0 for g in sigs):
                return False
        else:
            if not any(s + g + q == 0 for g in sigs for q in (1, -1)):
                return False
    return True


def run(S1, S2, F, samples=200, seed=1):
    rnd = random.Random(seed)
    OA, OB = orbit_points(S1), orbit_points(S2)
    nA, nB = S1 + 1, S2 + 1
    K = nA + nB + F
    found = 0
    tried = 0
    ex = []
    for vA, bA in OA:
        for vB, bB in OB:
            if accidental(vA, vB):
                continue
            for posA in combinations(range(K), nA):
                rest = [p for p in range(K) if p not in posA]
                for posB in combinations(rest, nB):
                    free = [p for p in rest if p not in posB]
                    seq = [None] * K
                    for p, x in zip(posA, vA):
                        seq[p] = x
                    for p, x in zip(posB, vB):
                        seq[p] = x
                    cyc = [(list(posA), bA), (list(posB), bB)]
                    if F == 0:
                        zs = [[]]
                    elif F == 1:
                        B = breakpoints(vA + vB)
                        zs = [[(a + b) / 2] for a, b in zip(B, B[1:])]
                    else:
                        zs = [[Fr(rnd.randrange(1, 10 ** 6), 10 ** 6 + 3) for _ in range(F)]
                              for _ in range(samples)]
                    for z in zs:
                        sq = list(seq)
                        for p, x in zip(free, z):
                            sq[p] = x
                        tried += 1
                        try:
                            ok = check(sq, cyc)
                        except ValueError:
                            continue
                        if ok:
                            found += 1
                            if len(ex) < 5:
                                ex.append(sq)
    print(f'S1={S1} S2={S2} F={F} (K={K}, m={S1 + S2 + 2}): {tried} configurations tried, '
          f'{found} valid', flush=True)
    for sq in ex:
        print('    ', ', '.join(str(x) for x in sq))
    return found


if __name__ == '__main__':
    S1, S2, F = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    samples = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    run(S1, S2, F, samples)
