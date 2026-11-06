"""core.py N1 N2 [rules]: the HARD CORE: non-dead pairs (u <= N+1-v) of [N] that are not inward
and lie in no copy (Beatty h <= 1 or its mirror, doubling split) with a NON-DEAD preimage.
Under strong induction on N (all non-dead pairs of smaller strips co-reachable) only these
need a special construction."""
import sys
from ucov import dead, inward, copies


def core(N, rules):
    good = set()
    for p, phi in copies(N, rules):
        for a in range(1, p + 1):
            for b in range(a + 1, p + 1):
                if not dead(p, a, b):
                    x, y = phi[a], phi[b]
                    good.add((x, y))
                    good.add((N + 1 - y, N + 1 - x))
    out = []
    for u in range(1, N + 1):
        for v in range(u + 1, N + 1):
            if u > N + 1 - v or dead(N, u, v) or inward(N, u, v) or (u, v) in good:
                continue
            if 'one' in rules and u == 1 and v == N and N % 2 == 1:
                continue
            out.append((u, v))
    return out


if __name__ == '__main__':
    rules = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else {'beatty', 'dbl', 'one', 'swap', 'chiY'}
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        c = core(N, rules)
        print(N, len(c), c, flush=True)
