# Doubling behaviour of r(n) from data/r_all_520.txt (window.bin all 520; agrees with the
# b-file to 5e-13 for n <= 200).  Usage: python3 doubling.py [file]
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
fn = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, 'data/r_all_520.txt')
r = {}
for l in open(fn):
    f = l.split(); r[int(f[0])] = float(f[1])
for n in range(4, 19):   # small n from the b-file
    pass
th = {int(a): int(b) for a, b in (l.split() for l in open(os.path.join(here, 'data/b003407.txt')))}
for n in range(2, 19):
    r[n] = th[n] / (2 * th[n // 2] * th[(n + 1) // 2])
M = max(r)
print("octave        max|r(2n)-r(n)|  ratio   max|r(2n+1)-(r(n)+r(n+1))/2|  ratio")
prev1 = prev2 = None
lo = 8
while 2 * lo + 1 <= M:
    hi = min(2 * lo, (M - 1) // 2 + 1)
    e1 = max(abs(r[2 * n] - r[n]) for n in range(lo, hi))
    e2 = max(abs(r[2 * n + 1] - (r[n] + r[n + 1]) / 2) for n in range(lo, hi))
    q1 = f"{prev1 / e1:5.2f}" if prev1 else "  -  "
    q2 = f"{prev2 / e2:5.2f}" if prev2 else "  -  "
    print(f"[{lo:4d},{hi:4d})   {e1:.3e}       {q1}    {e2:.3e}                   {q2}")
    prev1, prev2 = e1, e2
    lo *= 2
rng = [n for n in r if n >= 16]
print("min r(n), 16 <= n <= %d:" % M, min((r[n], n) for n in rng))
print("max r(n), 16 <= n <= %d:" % M, max((r[n], n) for n in rng))
for lo in (64, 128, 256):
    hi = min(2 * lo, M)
    print(f"  range on [{lo},{hi}]: {min(r[n] for n in range(lo, hi + 1)):.6f} .. "
          f"{max(r[n] for n in range(lo, hi + 1)):.6f}")
print("chains r(x 2^j):")
for x in (9, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33):
    print(f" x={x:2d}:", ' '.join(f"{r[x * 2**j]:.9f}" for j in range(8) if x * 2**j in r and x * 2**j >= 16))
