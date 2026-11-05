"""Three-body effective coupling for the doubling 3-cycle {k, 2k, 4k} (N = 7k, panel index m -> 2m mod N),
compared with the same triples at neighbouring N:
J3 = log[ a * a_{-12} a_{-13} a_{-23} / (a_{-1} a_{-2} a_{-3} a_{-123}) ]  (log interaction, inclusion-exclusion)."""
import os, subprocess, math, sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
cache = {}


def cnt(N, ps):
    key = (N, tuple(sorted(ps)))
    if key not in cache:
        cache[key] = int(subprocess.check_output([os.path.join(HERE, "dpx"), str(N)] + [str(p) for p in ps]))
    return cache[key]


def J3(N, T):
    s = 0.0
    for k in range(4):
        for sub in combinations(T, k):
            s += (-1) ** k * math.log(cnt(N, sub))
    return -s if False else s * (-1) ** 0  # sign: + for |sub| even


def J2(N, a, b):
    return math.log(cnt(N, ()) * cnt(N, (a, b)) / (cnt(N, (a,)) * cnt(N, (b,))))


if __name__ == "__main__":
    for N, T in [(14, (2, 4, 8)), (13, (2, 4, 8)), (15, (2, 4, 8)), (16, (2, 4, 8)),
                 (14, (7, 11, 13)), (13, (6, 10, 12)), (15, (8, 12, 14)),
                 (21, (3, 6, 12)), (20, (3, 6, 12)), (22, (3, 6, 12)), (23, (3, 6, 12)),
                 (21, (10, 16, 19)), (20, (9, 15, 18)), (22, (11, 17, 20)), (19, (3, 6, 12)), (24, (3, 6, 12))]:
        j3 = J3(N, T)
        print("N=%2d T=%s  J3=%+.4f   pair J: %s" % (N, T, j3, " ".join(
            "%d-%d:%+.3f" % (a, b, J2(N, a, b)) for a, b in combinations(T, 2))), flush=True)
