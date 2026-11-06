# Exact theta(n) = A003407(n) from residues (window_mod.bin) by the Chinese remainder theorem.
#   python3 crt.py primes K          print K primes just below 2^62
#   python3 crt.py combine NMAX f1 f2 ...   files "n residue" (first line of each file: "# p")
# The double-precision run (data/r_all_520.txt, column 3 = log theta) is used to check that
# the product of the primes exceeds theta(n) and that the reconstructed value has the right
# size; values n <= 200 are checked against the b-file.
import sys, os, math
here = os.path.dirname(os.path.abspath(__file__))

def is_prime(n):
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

if sys.argv[1] == 'primes':
    k, q = int(sys.argv[2]), (1 << 62) - 1
    out = []
    while len(out) < k:
        if is_prime(q): out.append(q)
        q -= 2
    print(' '.join(map(str, out)))
    sys.exit()

nmax = int(sys.argv[2])
res = {}
mods = []
for fn in sys.argv[3:]:
    lines = open(fn).read().split('\n')
    p = int(lines[0].split()[1]); mods.append(p)
    for l in lines[1:]:
        if l.strip():
            n, v = map(int, l.split()); res.setdefault(n, []).append((p, v))
logth = {}
for l in open(os.path.join(here, 'data/r_all_520.txt')):
    f = l.split(); logth[int(f[0])] = float(f[2])
bfile = {int(a): int(b) for a, b in (l.split() for l in open(os.path.join(here, 'data/b003407.txt')))}
M = math.prod(mods)
for n in sorted(res):
    if n > nmax or len(res[n]) != len(mods): continue
    x = 0
    for p, v in res[n]:
        Mp = M // p; x = (x + v * Mp * pow(Mp, -1, p)) % M
    assert math.log(M) > logth[n] + 5, f"not enough primes for n={n}"
    assert abs(math.log(x) - logth[n]) < 1e-6, f"size check failed n={n}"
    if n in bfile: assert bfile[n] == x, f"b-file mismatch n={n}"
    print(n, x)
