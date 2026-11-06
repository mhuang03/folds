# Check the halving recursion L_k(N) = L_k(ceil(N/2)) + L_k(floor(N/2)) for the number of
# extendable k-prefixes (THEOREM L in PROOFS.txt), and report the last N where it fails.
# usage: python3 lrec.py data/T_sym.txt data/T4_sym.txt
import sys
cols = {}
for line in open(sys.argv[1]):
    t = list(map(int, line.split()))
    cols.setdefault(2, {})[t[0]] = t[3]
    cols.setdefault(3, {})[t[0]] = t[4]
if len(sys.argv) > 2:
    for line in open(sys.argv[2]):
        t = list(map(int, line.split()))
        cols.setdefault(4, {})[t[0]] = t[2]
for k, L in sorted(cols.items()):
    fails = [N for N in L if N >= 2 and (N + 1) // 2 in L and N // 2 in L
             and L[N] != L[(N + 1) // 2] + L[N // 2]]
    print(f"k={k}: recursion fails at N = {sorted(fails)}; checked up to N = {max(L)}")
    print("   L_k(N)/N at N = 2^j:", [(N, round(L[N] / N, 4)) for N in L if N & (N - 1) == 0 and N >= 4])
