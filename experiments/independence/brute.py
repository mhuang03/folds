"""Brute-force pair independence for N <= 9 (light: at most 9! = 362880 orderings).

For every pair of panels (a, b) checks whether #(C_a and C_b) * N! == #C_a * #C_b, and
compares with the geometric classification:
  (a) disjoint windows;
  (b) for one panel a: b not in W_a, W_a meets W_b only inside one arm of b, the overlap
      contains a, and at most one element of W_a lies outside W_b.
Also reports which case (b) instances have exactly one outside element.
"""
import itertools
import sys


def reach(N, m):
    return min(m - 1, N - m)


def window(N, m):
    r = reach(N, m)
    return set(range(m - r, m + r + 1))


def arms(N, m):
    r = reach(N, m)
    return set(range(m - r, m)), set(range(m + 1, m + r + 1))


def case_b(N, a, b):
    Wa, Wb = window(N, a), window(N, b)
    if b in Wa:
        return None
    ov = Wa & Wb
    if a not in ov:
        return None
    L, R = arms(N, b)
    if not (ov <= L or ov <= R):
        return None
    out = len(Wa - Wb)
    return out if out <= 1 else None


def main(Nmax):
    for N in range(2, Nmax + 1):
        panels = range(1, N + 1)
        # sat[m] = bitmask over permutations index? use counts via enumeration
        cnt = {}
        single = {m: 0 for m in panels}
        pair = {}
        for perm in itertools.permutations(panels):
            pos = {x: i for i, x in enumerate(perm)}
            ok = []
            for m in panels:
                r = reach(N, m)
                lc = sum(1 for d in range(1, r + 1) if pos[m - d] < pos[m])
                rc = sum(1 for d in range(1, r + 1) if pos[m + d] < pos[m])
                ok.append(lc == rc)
            for i, m in enumerate(panels):
                if ok[i]:
                    single[m] += 1
            for i in range(N):
                if ok[i]:
                    for j in range(i + 1, N):
                        if ok[j]:
                            pair[(i + 1, j + 1)] = pair.get((i + 1, j + 1), 0) + 1
        import math
        F = math.factorial(N)
        bad = 0
        for a in panels:
            for b in panels:
                if a >= b:
                    continue
                joint = pair.get((a, b), 0)
                indep = joint * F == single[a] * single[b]
                disj = not (window(N, a) & window(N, b))
                cb = case_b(N, a, b)
                cb2 = case_b(N, b, a)
                pred = disj or cb is not None or cb2 is not None
                if indep != pred:
                    bad += 1
                    print(f"N={N} ({a},{b}) indep={indep} predicted={pred}")
                if (cb == 1) or (cb2 == 1):
                    print(f"N={N} one-outside pair ({a},{b}) indep={indep}")
        print(f"N={N}: mismatches={bad}")
        sys.stdout.flush()


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
