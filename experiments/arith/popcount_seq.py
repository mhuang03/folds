"""Popcount-ordered sequences: panels sorted by popcount (binary digit sum), ties by value.
Check validity for N = 1..200 and the descent count of the valid ones."""
from mim_util import valid


def check(seq, N):
    S = set()
    for m in seq:
        if not valid(S, m, N):
            return False
        S.add(m)
    return True


def des(s):
    return sum(s[i] > s[i + 1] for i in range(len(s) - 1))


def pc(m):
    return bin(m).count('1')


for name, key in [("pc desc, val asc ", lambda m: (-pc(m), m)),
                  ("pc asc,  val asc ", lambda m: (pc(m), m)),
                  ("pc desc, val desc", lambda m: (-pc(m), -m)),
                  ("pc asc,  val desc", lambda m: (pc(m), -m))]:
    fails = [N for N in range(1, 201) if not check(sorted(range(1, N + 1), key=key), N)]
    print(name, "invalid for", len(fails), "of N=1..200; first:", fails[:15])

ok = all(des(sorted(range(1, N + 1), key=lambda m: (-pc(m), m))) == (N + 1).bit_length() - 2
         for N in range(1, 201))
print("des(pc desc, val asc) == floor(log2(N+1)) - 1 for all N<=200:", ok)
