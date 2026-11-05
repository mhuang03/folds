"""orderset.py N x y ...: an ordering from scratch of [N] minus the given panels (built backwards
with the reachability bitset: repeatedly remove the largest/smallest valid last element)."""
import sys
from lib import reachable, valid_step


def order(N, T, pref=max):
    T = set(T)
    if not reachable(N, T):
        return None
    out = []
    while T:
        cands = [m for m in T if valid_step(N, T - {m}, m) and reachable(N, T - {m})]
        m = pref(cands)
        out.append(m)
        T.remove(m)
    return out[::-1]


if __name__ == '__main__':
    N = int(sys.argv[1])
    D = set(int(a) for a in sys.argv[2:])
    print(order(N, set(range(1, N + 1)) - D))
