"""Generalised composition test: residue classes mod d of [N] (d need not divide N).
For a class order pi (permutation of residues), check the two block conditions of the
sub-block lemma for every class C_s in turn:
  (i)  C_s is self-balanced (each z in C_s has equally many C_s-elements in both arms);
  (ii) the union W of the earlier classes is balanced around every z in C_s.
If both hold for all classes, any strip-valid inner orders work, and
a(N) >= (#good pi) * prod a(|C_s|)."""
import sys, itertools
def arms(N, m):
    r = min(m - 1, N - m)
    return range(m - r, m), range(m + 1, m + r + 1)
def balanced(N, W, m):
    L, R = arms(N, m)
    return sum(1 for x in L if x in W) == sum(1 for x in R if x in W)
def selfbal(N, Z):
    return all(balanced(N, Z - {z}, z) for z in Z)
def classes(N, d):
    return {s: set(range(s, N + 1, d)) for s in range(1, d + 1)}
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for d in range(2, 7):
        if d > N: continue
        C = classes(N, d)
        sb = {s: selfbal(N, C[s]) for s in C}
        good = 0
        for pi in itertools.permutations(range(1, d + 1)):
            W = set(); ok = True
            for s in pi:
                if not sb[s] or not all(balanced(N, W, z) for z in C[s]):
                    ok = False; break
                W |= C[s]
            good += ok
        print(N, d, "N%d=" % d, N % d, "selfbal:", "".join("1" if sb[s] else "0" for s in sorted(C)), "good orders:", good)
