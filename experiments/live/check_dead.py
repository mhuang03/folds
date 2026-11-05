"""check_dead.py dead.txt: compare the computed dead 1-, 2-, 3-prefixes (output of `live`)
with the conjectured characterization.

Dead 2-prefixes: (1,N), (N,1) for even N >= 4, and also for N = 7.
Dead 3-prefixes (N = 6 and N >= 8): the valid orderings of the dead 3-sets
  D_j = {1, 2j, 2j+1} and its mirror {N, N+1-2j, N-2j},   2 <= j <= floor((N+1)/4),
  and, for odd N, the four 3-subsets of {1, 2, N-1, N}.
(For even N the 3-prefixes through the dead pair (1,N) do not exist: no valid third step.)
Each D_j has exactly one valid ordering (2j+1, 1, 2j), except j = h when N in {4h-1, 4h},
where (1, 2h+1, 2h) is valid too; each 3-subset of {1,2,N-1,N} has exactly three valid
orderings.  Count: 2(floor((N+1)/4) - 1) + 2[N mod 4 in {0,3}] + 12[N odd]."""
import sys
from collections import defaultdict


def ok(N, S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
        sum(1 for d in range(1, r + 1) if (m + d) in S)


def valid(N, a):
    return all(ok(N, set(a[:k]), a[k]) for k in range(len(a)))


def dead_sets(N):
    D = set()
    for j in range(2, (N + 1) // 4 + 1):
        D.add(frozenset({1, 2 * j, 2 * j + 1}))
        D.add(frozenset({N, N + 1 - 2 * j, N - 2 * j}))
    if N % 2 == 1:
        c = [1, 2, N - 1, N]
        for i in range(4):
            D.add(frozenset(c[:i] + c[i + 1:]))
    return D


def predicted3(N):
    from itertools import permutations
    out = set()
    for s in dead_sets(N):
        for p in permutations(sorted(s)):
            if valid(N, p):
                out.add(p)
    return out


def predicted_count(N):
    return 2 * ((N + 1) // 4 - 1) + 2 * (N % 4 in (0, 3)) + 12 * (N % 2)


d1, d2, d3 = defaultdict(set), defaultdict(set), defaultdict(set)
Ns = set()
for line in open(sys.argv[1]):
    w = line.split()
    if w[0] == "dead1":
        d1[int(w[1])].add(int(w[2]))
    elif w[0] == "dead2":
        d2[int(w[1])].add((int(w[2]), int(w[3])))
    elif w[0] == "dead3":
        d3[int(w[1])].add(tuple(map(int, w[2:5])))
    elif w[0] == "summary":
        Ns.add(int(w[1].split("=")[1]))
allok = True
for N in sorted(Ns):
    p2 = {(1, N), (N, 1)} if (N % 2 == 0 and N >= 4) or N == 7 else set()
    ok1 = not d1[N]
    ok2 = d2[N] == p2
    if N == 6 or N >= 8:
        ok3 = d3[N] == predicted3(N) and len(d3[N]) == predicted_count(N)
    else:
        ok3 = None
    print(N, "dead1 none" if ok1 else d1[N], "dead2 ok" if ok2 else ("dead2", d2[N]),
          "dead3", len(d3[N]), {True: "ok", False: "MISMATCH", None: "(small N)"}[ok3])
    allok &= ok1 and ok2 and ok3 is not False
print("ALL OK" if allok else "FAILURES")
