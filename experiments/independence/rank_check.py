"""Check the key lemma of the one-outside case (PROOFS.txt section 4), for N = 2n+2 <= 10.

b = n+2 has window [2, N]; L = [2, n+1] is its left arm.  Claim: the number of orderings
satisfying C_b, among those in which panel 1 has rank i in L u {1}, does not depend on i.
Counted over orderings of the relevant panels only (all of [1..N]).
"""
import itertools
import sys


def main(Nmax):
    for N in range(4, Nmax + 1, 2):
        n = (N - 2) // 2
        b = n + 2
        L = list(range(2, n + 2))
        R = list(range(n + 3, N + 1))
        counts = [0] * (n + 1)
        for perm in itertools.permutations(range(1, N + 1)):
            pos = {x: k for k, x in enumerate(perm)}
            lc = sum(1 for x in L if pos[x] < pos[b])
            rc = sum(1 for x in R if pos[x] < pos[b])
            if lc == rc:
                i = sum(1 for x in L if pos[x] < pos[1])
                counts[i] += 1
        print(f"N={N}: C_b counts by rank of 1 among L+{{1}}: {counts}")
        sys.stdout.flush()


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
