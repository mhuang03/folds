"""Tabulate out/cuts_*.txt (output of cutmat.bin) as compact tables.
usage: python3 table.py out/cuts_2_13.txt [more files]"""
import re
import sys
from math import factorial

rows = []
for fn in sys.argv[1:]:
    for line in open(fn):
        m = re.match(r'N=(\d+) cut=(\S+) \|X\|=(\d+) \|Y\|=(\d+) a=(\d+) \| all: nzr=(\d+) nzc=(\d+) dr=(\d+) '
                     r'dc=(\d+) rank=(\d+) .*valid x valid: vr=(\d+) vc=(\d+) nzr=(\d+) nzc=(\d+) dr=(\d+) '
                     r'dc=(\d+) rank=(\d+) sum=(\d+)', line)
        if m:
            g = m.groups()
            rows.append((int(g[0]), g[1]) + tuple(int(x) for x in g[2:]))


def show(pred, title):
    print(title)
    print('  N  cut          |X| |Y|   |X|!    |Y|!     nzr     nzc      dr      dc    rank  full? |'
          '   vr    vc   Vdr   Vdc Vrank   Vsum/a')
    for r in rows:
        (N, cut, kx, ky, a, nzr, nzc, dr, dc, rank, vr, vc, vnzr, vnzc, vdr, vdc, vrank, vsum) = r
        if not pred(N, cut, kx, ky):
            continue
        full = 'yes' if rank == min(dr, dc) else 'NO'
        print('%3d  %-12s %3d %3d %6d %7d %7d %7d %7d %7d %7d  %-4s | %5d %5d %5d %5d %5d   %.4f'
              % (N, cut, kx, ky, factorial(kx), factorial(ky), nzr, nzc, dr, dc, rank, full,
                 vr, vc, vdr, vdc, vrank, vsum / a))
    print()


show(lambda N, c, kx, ky: c == 'parity', 'PARITY CUT (X = odd panels)')
show(lambda N, c, kx, ky: c.startswith('spatial') and kx == N // 2, 'SPATIAL MIDDLE CUT (X = [1, floor(N/2)])')
show(lambda N, c, kx, ky: c.startswith('spatial') and kx <= N // 2 and N >= 11, 'SPATIAL CUTS X = [1, j], j <= N/2, N >= 11')
show(lambda N, c, kx, ky: c.startswith('res_3'), 'RESIDUE CUTS mod 3 (X = {x : x mod 3 = r})')
show(lambda N, c, kx, ky: c.startswith('res_4'), 'RESIDUE CUTS mod 4')
show(lambda N, c, kx, ky: c.startswith('ed'), 'NEUTRAL SETS X = E_d')

# rank of the spatial cut j as a function of N
print('SPATIAL CUT: rank by (N, j)')
tab = {}
for r in rows:
    if r[1].startswith('spatial'):
        tab[(r[0], r[2])] = (r[9], r[7], r[5])
Ns = sorted({k[0] for k in tab})
for N in Ns:
    print('%3d rank: ' % N + ' '.join('%5d' % tab[(N, j)][0] for j in range(1, N)))
    print('    dr:   ' + ' '.join('%5d' % tab[(N, j)][1] for j in range(1, N)))
    print('    nzr:  ' + ' '.join('%5d' % tab[(N, j)][2] for j in range(1, N)))
