"""classify.py FILE: list the DEAD / UNRESOLVED sets of an ek output that are not explained by a
known family (with mirror images).  Families:
  B2  {1} + {2j, 2j+1}, nothing of D in [2, 2j-1]                  (contains an end panel)
  B4  {2} + {2j, ..., 2j+3}, 1 not in D, nothing of D in [3, 2j-1]
  END D contains 1 or N
"""
import sys, re


def b4(D, N):
    if 2 not in D or 1 in D:
        return False
    rest = sorted(x for x in D if x > 2)
    if not rest:
        return False
    a = rest[0]
    return a % 2 == 0 and a >= 6 and all(a + i in D for i in range(4))


def fam(D, N):
    M = set(N + 1 - x for x in D)
    if 1 in D or N in D:
        return 'END'
    if b4(D, N) or b4(M, N):
        return 'B4'
    return None


def main():
    for line in open(sys.argv[1]):
        m = re.match(r'\s*(DEAD|UNRESOLVED) N=(\d+):([\d ]+)\(', line)
        if not m:
            continue
        N = int(m.group(2))
        D = set(map(int, m.group(3).split()))
        if fam(D, N) is None:
            print(m.group(1), N, sorted(D))


main()
