"""sym.py a [r]: the symmetric sporadic sets S_a = {a, N+1-a} + [2a+2, N-2a-1], N = 6a + r
(r = 0 or 1).  Exhaustive search over all placements on the background S_a (N small), and a
summary of the reachable states: for each, the placed panels of G_L = [a+1, 2a+1] and of
G_R = [N-2a, N-a], and the numbers pL, pR of placed panels in [1, a-1] and [N+2-a, N].
"""
import sys


def main():
    a = int(sys.argv[1])
    r = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    N = 6 * a + r
    D = {a, N + 1 - a} | set(range(2 * a + 2, N - 2 * a))
    free = [m for m in range(1, N + 1) if m not in D]

    def reach(m):
        return min(m - 1, N - m)

    start = frozenset(D)
    seen = {start}
    stack = [start]
    while stack:
        S = stack.pop()
        for m in free:
            if m in S:
                continue
            rr = reach(m)
            lc = sum(1 for x in S if m - rr <= x < m)
            rc = sum(1 for x in S if m < x <= m + rr)
            if lc == rc:
                T = S | {m}
                if T not in seen:
                    seen.add(T)
                    stack.append(T)
    full = frozenset(range(1, N + 1))
    print(f"a={a} N={N} D={sorted(D)}: {len(seen)} reachable states; complete: {full in seen}")
    GL = set(range(a + 1, 2 * a + 2))
    GR = set(range(N - 2 * a, N - a + 1))
    summ = set()
    for S in seen:
        pL = len(S & set(range(1, a)))
        pR = len(S & set(range(N + 2 - a, N + 1)))
        summ.add((pL, tuple(sorted(S & GL)), pR, tuple(sorted(S & GR))))
    best = max(len(x[1]) + len(x[3]) for x in summ)
    print(f"  max placed of G_L + G_R: {best} of {len(GL) + len(GR)}")
    for x in sorted(summ, key=lambda x: (len(x[1]) + len(x[3]), x))[-12:]:
        print("   pL=%d GL=%s pR=%d GR=%s" % x)


main()
