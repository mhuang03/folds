# one3N.py NMAX: check the closed-form near maps for {1, 3, N} (and the mirror {1, N-2, N})
# for every N <= NMAX in each residue class mod 4 (section 2 of PROOFS.txt).
import sys
from nb import *
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200

def check_two(N, p, phi, D, q, psi, i1, i2):
    """phi : [p] -> [N] regular outside D, image complement = psi([q]) regular outside i1, i2,
    [i1, i2] valid in [q], [psi i1, psi i2] valid in [N], {i1, i2} not dead"""
    img = {phi(y) for y in range(1, p + 1)}; Y = {psi(i) for i in range(1, q + 1)}
    ok = increasing(N, p, phi) and increasing(N, q, psi) and img | Y == set(range(1, N + 1))
    ir = set(irregular(N, p, phi)); ir2 = set(irregular(N, q, psi))
    pre = sorted(D)
    v = (valid(q, {i1}, i2) and valid(N, {psi(i1)}, psi(i2)) and
         not deadpair(q, min(i1, i2), max(i1, i2)) and valid3(p, *pre) and not dead3(p, *pre))
    return ok and ir <= set(D) and ir2 <= {i1, i2} and v

bad = []
# N = 1 mod 4: N = 2p + 1, p even
for N in range(17, NMAX + 1, 4):
    p = (N - 1) // 2
    phi = lambda y: 1 if y == 1 else 3 if y == 2 else N if y == p else 2 * y
    psi = lambda i: 2 if i == 1 else 4 if i == 2 else 2 * p if i == p + 1 else 2 * i - 1
    if not check_two(N, p, phi, {1, 2, p}, p + 1, psi, 2, p + 1): bad.append(N)
print('N = 1 mod 4: failures', bad)
