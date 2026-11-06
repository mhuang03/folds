# Exact ratios r(n) = theta(n) / (2 theta(floor n/2) theta(ceil n/2)) from the b-file, and the
# test of Conjecture R' (../symratio/PROOFS.txt section 6):
#   for odd x, r(x 2^j) = Phi(x) + A(x) 4^-j + o(4^-j), with A(x) = 0 when 3 | x
#   (then super-geometric convergence).
# Usage: python3 ratios.py [b-file] [ratios-out]     (defaults: b003407.txt, ratios.txt)
import sys, os
from fractions import Fraction
from decimal import Decimal, getcontext
getcontext().prec = 80
here = os.path.dirname(os.path.abspath(__file__))
bfn = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, 'b003407.txt')
rfn = sys.argv[2] if len(sys.argv) > 2 else os.path.join(here, 'ratios.txt')
th = {int(a): int(b) for a, b in (l.split() for l in open(bfn))}
N = max(th)
R = {n: Fraction(th[n], 2 * th[n // 2] * th[(n + 1) // 2]) for n in range(2, N + 1)}
def dec(q): return Decimal(q.numerator) / Decimal(q.denominator)
with open(rfn, 'w') as f:
    f.write("# n  r(n) = theta(n)/(2 theta(floor n/2) theta(ceil n/2))  (40 digits, exact b-file)\n")
    for n in range(2, N + 1): f.write(f"{n} {dec(R[n]):.40f}\n")

def e(x): return f"{float(x):+.3e}" if x != 0 else "0"
old = {}
try:
    for l in open(os.path.join(here, '../symratio/data/r_all_520.txt')):
        a = l.split(); old[int(a[0])] = float(a[1])
    for l in open(os.path.join(here, '../symratio/data/chains.txt')):
        a = l.split(); old[int(a[0])] = float(a[1])
except OSError: pass
common = [n for n in old if n in R]
if common:
    err = max(abs(float(R[n]) - old[n]) for n in common)
    print(f"double-precision window.bin values (r_all_520, chains): {len(common)} n, max |diff| = {err:.2e}")

rng = [n for n in R if n >= 16]
mn = min(rng, key=lambda n: R[n]); mx = max(rng, key=lambda n: R[n])
print(f"16 <= n <= {N}:  min r = {float(R[mn]):.9f} (n={mn}),  max r = {float(R[mx]):.9f} (n={mx})")
lo = 64
while 2 * lo <= N:
    seg = range(lo, min(2 * lo, N) + 1)
    print(f"  octave [{lo},{min(2*lo, N)}]: {float(min(R[n] for n in seg)):.7f} .. {float(max(R[n] for n in seg)):.7f}")
    lo *= 2

print("\nDoubling contraction, max over each octave of n:")
print("  octave        max|r(2n)-r(n)|  ratio   max|r(2n+1)-(r(n)+r(n+1))/2|  ratio")
p1 = p2 = None; lo = 8
while 2 * lo + 1 <= N:
    hi = min(2 * lo, (N - 1) // 2 + 1)
    e1 = max(abs(R[2 * n] - R[n]) for n in range(lo, hi))
    e2 = max(abs(R[2 * n + 1] - (R[n] + R[n + 1]) / 2) for n in range(lo, hi))
    q1 = f"{float(p1 / e1):5.2f}" if p1 else "  -  "
    q2 = f"{float(p2 / e2):5.2f}" if p2 else "  -  "
    part = "" if hi == 2 * lo else "  (partial)"
    print(f"  [{lo:4d},{hi:4d})   {float(e1):.3e}       {q1}    {float(e2):.3e}                   {q2}{part}")
    p1, p2 = e1, e2; lo *= 2

print("\nChains x 2^j (x odd, x 2^j >= 16): differences D_j = r(x 2^{j+1}) - r(x 2^j)")
print("  3 does not divide x: ratios D_j / D_{j+1} (R' predicts -> 4);")
print("  3 | x: log|D_{j+1}| / log|D_j| (2 would be quadratic convergence).")
for x in range(1, N // 32 + 1, 2):
    ns = [x * 2 ** j for j in range(20) if 16 <= x * 2 ** j <= N]
    if len(ns) < 4: continue
    D = [R[ns[i + 1]] - R[ns[i]] for i in range(len(ns) - 1)]
    s = f"  x={x:3d} n={ns[0]}..{ns[-1]}  r(last)={dec(R[ns[-1]]):.15f}\n      D: " + ' '.join(e(d) for d in D)
    if x % 3:
        s += "\n      ratios: " + ' '.join(f"{float(D[i] / D[i + 1]):.4f}" if D[i + 1] else "inf" for i in range(len(D) - 1))
        phi = R[ns[-1]] + D[-1] / 3
        s += f"\n      Richardson Phi = r(last) + D_last/3 = {dec(phi):.12f}"
    else:
        import math
        lg = [math.log10(abs(float(d))) if d else None for d in D]
        s += "\n      log10|D|: " + ' '.join(f"{v:.2f}" if v is not None else "-inf" for v in lg)
        s += "\n      log|D_j+1|/log|D_j|: " + ' '.join(
            f"{lg[i + 1] / lg[i]:.3f}" for i in range(len(lg) - 1) if lg[i] and lg[i + 1] and lg[i] < -1.5)
    print(s)
