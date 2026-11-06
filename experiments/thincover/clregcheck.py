"""clregcheck.py FILE NMIN NMAX : for the cluster regions of clpieces (A, B, D, C by the lines AL, BL, CD)
the minimal window width of the region's certificate over the cells of the region (clwidth columns
0..3 = a, b, c, d), and the worst cells."""
import sys
from collections import defaultdict

nmin, nmax = int(sys.argv[2]), int(sys.argv[3])
col = {'A': 0, 'B': 1, 'C': 2, 'D': 3}
worst = defaultdict(list)
for line in open(sys.argv[1]):
    a = line.split()
    N, r, d = int(a[0]), int(a[1]), int(a[2])
    if not (nmin <= N <= nmax):
        continue
    ws = [float(x) for x in a[4:8]]
    AL = 50 * d + 31 * r - 825
    BL = -(10 * d + 13 * r + 130)
    CD = -(d + r + 1)          # 2v - 3u = -(delta + r + 1)
    regs = []
    if AL >= 0:
        regs.append('A')
    if BL >= 0:
        regs.append('B')
    if AL <= 0 and BL <= 0 and CD >= 0:
        regs.append('D')
    if AL <= 0 and BL <= 0 and CD <= -1:
        regs.append('C')
    for R in regs:
        worst[R].append((ws[col[R]], N, r, d))
for R in 'ABCD':
    L = sorted(worst[R])
    print(R, len(L), L[:8])
