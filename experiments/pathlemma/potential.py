"""potential.py PATHFILE N : checks the |J| potential identity of PROOFS.txt section 3 on a path.
Phi_k = sum over free panels of |J_k(m)|.  At step k, among the free panels m != x_k in the
dipole support of x_k: Z = #(J = 0), A = #(J != 0, kick of the same sign), B = #(opposite sign).
Identity: sum_k B_k = sum_k (Z_k + A_k); hence sum_k (A_k + B_k) >= (1/2) sum_k (Z_k + A_k + B_k)."""
import sys
f = sys.argv[1]; N = int(sys.argv[2]); seq = [int(l) for l in open(f)]
J = [0] * (N + 2); inS = [0] * (N + 2)
SZ = SA = SB = 0
for k, x in enumerate(seq):
    assert J[x] == 0
    for m in range(1, N + 1):
        if inS[m] or m == x: continue
        if m < x <= 2 * m - 1: kick = 1
        elif 2 * m - N <= x < m: kick = -1
        else: continue
        if J[m] == 0: SZ += 1
        elif (J[m] > 0) == (kick > 0): SA += 1
        else: SB += 1
    inS[x] = 1
    for q in range(x // 2 + 1, x): J[q] += 1
    for q in range(x + 1, (N + x) // 2 + 1): J[q] -= 1
print("N=%d  sum Z=%d  sum A=%d  sum B=%d  (B == Z + A: %s)  nonzero share in windows %.3f" % (
    N, SZ, SA, SB, SB == SZ + SA, (SA + SB) / (SZ + SA + SB)))
