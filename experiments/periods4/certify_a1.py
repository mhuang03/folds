"""certify_a1.py SMIN SMAX: certify.py for a = 1 only (q = 2(2^s - 1), k = s + 2)."""
import sys
from certify import certify

for s in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    how, main, tail, dt = certify(s, 1)
    print(f'k={s + 2:2d} s={s:2d} a= 1 q={2 * (2 ** s - 1):9d}  {how:40s} |main|/M0={main:.6g}  '
          f'tail/M0<={tail:.4g}  margin={main / tail if tail else float("inf"):.3g}  ({dt:.0f}s)', flush=True)
