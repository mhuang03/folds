"""classify.py FILE [FILE ...]: the DEAD / UNRESOLVED sets of ek outputs, classified.
  BA  the anchored-block family of Lean `Ek.not_coReach_anchor` (or its mirror image):
      some a in D and j >= a + 1 with [2j, 2j+2a-1] in D, nothing of D in [a+1, 2j-1],
      2j + 2a - 1 <= N.  (a = 1: the blocks {1, 2j, 2j+1}; a = 2: the B4 family.)
  END D contains 1 or N (only possible for lo = 1 runs).
Prints a summary per file and every set not in BA.
"""
import sys, re


def ba(D, N):
    for a in sorted(D):
        for j in range(a + 1, N):
            if 2 * j + 2 * a - 1 > N:
                break
            if all(2 * j + t in D for t in range(2 * a)) and \
                    not any(a < x < 2 * j for x in D):
                return (a, j)
    return None


def fam(D, N):
    M = set(N + 1 - x for x in D)
    r = ba(D, N)
    if r:
        return 'BA(a=%d,j=%d)' % r
    r = ba(M, N)
    if r:
        return 'BA-mirror(a=%d,j=%d)' % r
    if 1 in D or N in D:
        return 'END'
    return None


def main():
    for fn in sys.argv[1:]:
        tot = expl = 0
        rest = []
        for line in open(fn):
            m = re.match(r'\s*(DEAD\S*|UNRESOLVED) N=(\d+):([\d ]+)\(', line)
            if not m:
                continue
            N = int(m.group(2))
            D = set(map(int, m.group(3).split()))
            tot += 1
            f = fam(D, N)
            if f and f != 'END':
                expl += 1
            else:
                rest.append((m.group(1), N, sorted(D), f))
        print(f"{fn}: {tot} reported sets, {expl} in BA (or mirror), {len(rest)} others")
        for r in rest:
            print("   ", *r)


main()
