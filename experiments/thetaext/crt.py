# Exact theta(n) = A003407(n) from the residue files of theta.bin, by the Chinese remainder
# theorem, with redundancy and cross-checks.
#   python3 crt.py primes K [SKIP]      K primes just below 2^61 (skipping the first SKIP)
#   python3 crt.py combine OUT f1 f2 ...
#       files: "# p1 .. pK" header, lines "n r1 .. rK" (theta.bin output).  Writes the
#       b-file OUT (lines "n theta(n)", n = 0..max) and prints a check report.
# Bound used (proved): for n >= 14, theta(n) <= 2 * 924 * theta(floor n/2) * theta(ceil n/2)
# (Theorem M + Theorem W of ../symratio/PROOFS.txt: theta(n) = sum_p sum_{sigma,tau}
# Pi(window) and Pi <= C(12,6) = 924; Lean SymRatio.card_symSeqs_eq_win_sum).  For every n
# we require  prod(primes) > 2^61 * bound(n),  so the reconstruction is exact and the extra
# >= 61 bits act as a redundancy check: a wrong residue would give a CRT value that is
# uniformly spread in [0, M) and would exceed bound(n) except with probability < 2^-61.
import sys, os, math
here = os.path.dirname(os.path.abspath(__file__))

def is_prime(n):
    if n < 2: return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in small:          # deterministic for n < 3.3e24
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

if sys.argv[1] == 'primes':
    k = int(sys.argv[2]); skip = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    q, out = (1 << 61) - 1, []
    while len(out) < k + skip:
        if is_prime(q): out.append(q)
        q -= 2
    print(' '.join(map(str, out[skip:])))
    sys.exit()

assert sys.argv[1] == 'combine'
outfn = sys.argv[2]
res = {}
mods = []
for fn in sys.argv[3:]:
    ps = None
    for l in open(fn):
        f = l.split()
        if not f: continue
        if f[0] == '#': ps = list(map(int, f[1:])); mods += ps; continue
        n = int(f[0]); vals = list(map(int, f[1:]))
        assert len(vals) == len(ps), (fn, n)
        res.setdefault(n, {}).update(zip(ps, vals))
assert len(set(mods)) == len(mods), "duplicate primes"
for p in mods: assert is_prime(p) and p < 2 ** 61
M = math.prod(mods)
bfile = {int(a): int(b) for a, b in (l.split() for l in open(os.path.join(here, '../symratio/data/b003407.txt')))}
old = {int(a): int(b) for a, b in (l.split() for l in open(os.path.join(here, '../symratio/data/theta_exact.txt')))}
theta = {n: bfile[n] for n in range(0, 9)}
nmax = max(n for n in res if len(res[n]) == len(mods))
coef = [(p, (M // p) * pow(M // p, -1, p)) for p in mods]
nb = no = 0
for n in range(9, nmax + 1):
    r = res[n]; assert len(r) == len(mods), f"missing residues for n={n}"
    x = sum(r[p] * c for p, c in coef) % M
    if n >= 19:
        bound = 2 * 924 * theta[n // 2] * theta[(n + 1) // 2]
        assert M > (1 << 61) * bound, f"not enough primes for n={n}"
        assert x <= bound, f"redundancy check failed at n={n}"
        assert x >= 2 * theta[n // 2] * theta[(n + 1) // 2], f"lower check failed n={n}"
    else:
        assert x < 10 ** 7
    if n in bfile: assert bfile[n] == x, f"b-file mismatch n={n}"; nb += 1
    if n in old: assert old[n] == x, f"theta_exact mismatch n={n}"; no += 1
    theta[n] = x
with open(outfn, 'w') as f:
    for n in range(0, nmax + 1): f.write(f"{n} {theta[n]}\n")
print(f"{len(mods)} primes, log2(M) = {math.log2(M):.1f}; n = 0..{nmax}")
print(f"agree with the OEIS b-file: {nb} values (9 <= n <= 200), with symratio theta_exact: {no}")
print(f"theta({nmax}) has {len(str(theta[nmax]))} digits; "
      f"max log2 bound needed {math.log2(2*924*theta[nmax//2]*theta[(nmax+1)//2]) + 61:.1f} bits")
