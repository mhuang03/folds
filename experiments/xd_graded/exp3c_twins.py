"""Experiment 3c: 'twin' live sets (same unique live successor) and the death depth of their
other successors.  Usage: python3 exp3c_twins.py N [N ...]

For each N lists pairs of live k-sets (k < N/2) S != S' whose only live up-neighbour is one
common set T: such a pair is a Hall violator of size 2, so no weighting of the edges of the
live graph can make U injective on rank k.  For the first pair found at each rank, prints
all valid additions of S and S', and for each dead successor its death depth (the fuel needed
by the recursive deadness check: depth 0 = no valid addition at all).
"""
import sys
from common import masks, gtable


def setstr(S, N):
    return "{" + ",".join(str(m) for m in range(1, N + 1) if S >> (m - 1) & 1) + "}"


def main(N):
    L, R = masks(N)
    g, pc = gtable(N)
    full = (1 << N) - 1

    def ups(S):
        return [m for m in range(1, N + 1) if not S >> (m - 1) & 1
                and pc[S & L[m]] == pc[S & R[m]]]

    depth_cache = {}

    def death_depth(S):
        """None if S is co-reachable (a valid chain to [N] exists); else the fuel needed."""
        if S == full:
            return None
        if S in depth_cache:
            return depth_cache[S]
        d = 0
        for m in ups(S):
            x = death_depth(S | 1 << (m - 1))
            if x is None:
                depth_cache[S] = None
                return None
            d = max(d, x + 1)
        depth_cache[S] = d
        return d

    live = [S for S in range(1 << N) if g[S] and g[full ^ S]]
    by_succ = {}
    for S in live:
        k = pc[S]
        if 2 * k >= N:
            continue
        succ = [S | 1 << (m - 1) for m in ups(S)]
        lsucc = [T for T in succ if g[full ^ T]]
        if len(lsucc) == 1:
            by_succ.setdefault((k, lsucc[0]), []).append(S)
    twins = {key: v for key, v in by_succ.items() if len(v) >= 2}
    print(f"N={N}: {len(twins)} twin groups; by rank:",
          {k: sum(1 for key in twins if key[0] == k) for k in sorted({key[0] for key in twins})})
    shown = set()
    for (k, T), v in sorted(twins.items()):
        if k in shown:
            continue
        shown.add(k)
        print(f"  rank {k}: {[setstr(S, N) for S in v]} -> {setstr(T, N)}")
        for S in v:
            for m in ups(S):
                X = S | 1 << (m - 1)
                print(f"     {setstr(S, N)} + {m}: death depth {death_depth(X)}")


if __name__ == '__main__':
    for a in sys.argv[1:]:
        main(int(a))
