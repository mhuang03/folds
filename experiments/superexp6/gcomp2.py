"""List the good class orders of the generalised composition (see gcomp.py) and test
candidate rules.  Classes are labelled by their least element s in [1, d]."""
import sys, itertools
def arms(N, m):
    r = min(m - 1, N - m)
    return range(m - r, m), range(m + 1, m + r + 1)
def balanced(N, W, m):
    L, R = arms(N, m)
    return sum(1 for x in L if x in W) == sum(1 for x in R if x in W)
def good(N, d, pi):
    W = set()
    for s in pi:
        C = set(range(s, N + 1, d))
        if not all(balanced(N, C - {z}, z) for z in C): return False
        if not all(balanced(N, W, z) for z in C): return False
        W |= C
    return True
if __name__ == "__main__":
    d = int(sys.argv[1])
    for N in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
        gs = [pi for pi in itertools.permutations(range(1, d + 1)) if good(N, d, pi)]
        print(N, N % d, len(gs), " ".join("".join(map(str, p)) for p in gs[:12]))
