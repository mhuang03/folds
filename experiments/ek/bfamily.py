"""bfamily.py a j: the local game for the family B_a = {a} + [2j, 2j+2a-1] (nothing else of D in
[1, 2j-1]; panels beyond the block are ignored, wildcards are not needed since every core window
[1, 2m-1] with m <= 2j-1 lies inside [1, 4j-3] and we take N large and D = B_a exactly on
[1, 4j-3]).  Free panels in [2j+2a, 4j-3] are wildcards (placed at will).
Prints the reachable states' maximum number s of placed panels of G = [a+1, 2j-1], whether all of
G can be placed (i.e. whether B_a is locally dead), and checks the invariants
   (I1) every placed G-panel is in [j+1, j+p], p = number of placed panels of [1, a-1];
   (I2) s <= p.
"""
import sys


def main():
    a, j = int(sys.argv[1]), int(sys.argv[2])
    W = 4 * j - 3
    D = {a} | set(range(2 * j, 2 * j + 2 * a))
    core = [m for m in range(1, 2 * j) if m not in D]
    wild = [m for m in range(2 * j, W + 1) if m not in D]
    start = frozenset(x for x in D if x <= W)
    seen = {start}
    stack = [start]
    maxs = 0
    ok1 = ok2 = True
    G = set(range(a + 1, 2 * j))
    while stack:
        S = stack.pop()
        s = len(S & G)
        p = len(S & set(range(1, a)))
        maxs = max(maxs, s)
        if not all(j + 1 <= x <= j + p for x in S & G):
            ok1 = False
        if s > p:
            ok2 = False
        for m in core + wild:
            if m in S:
                continue
            if m in core:
                lc = sum(1 for x in S if 1 <= x < m)
                rc = sum(1 for x in S if m < x <= 2 * m - 1)
                if lc != rc:
                    continue
            T = S | {m}
            if T not in seen:
                seen.add(T)
                stack.append(T)
    print(f"a={a} j={j}: states={len(seen)} max placed of G = {maxs} of {len(G)};"
          f" locally dead: {maxs < len(G)}; I1 {ok1}; I2 {ok2}")


main()
