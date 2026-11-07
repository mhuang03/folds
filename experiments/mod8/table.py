"""Residue tables: a(N), c(N) mod 8 / 16, and the self-dual middle split (sdmid_out.txt).
usage: python3 table.py   (run from experiments/mod8)"""
import os
here = os.path.dirname(os.path.abspath(__file__))
a, c, outer = {}, {}, {}
for l in open(os.path.join(here, '..', 'semi_counts.txt')):
    if l.startswith('#'):
        continue
    p = l.split()
    a[int(p[0])] = int(p[1])
for l in open(os.path.join(here, '..', 'arith', 'selfdual_out.txt')):
    p = l.split()
    c[int(p[0])] = int(p[1])
small = {4: (6, 4), 6: (12, 8), 8: (76, 64), 10: (274, 204), 12: (1088, 864), 14: (5696, 4172),
         16: (39484, 27612), 18: (176338, 123684)}
for N, (cc, o) in small.items():
    outer[N] = o
fn = os.path.join(here, 'sdmid_out.txt')
if os.path.exists(fn):
    for l in open(fn):
        p = l.split()
        if len(p) >= 4 and p[0].isdigit():
            outer[int(p[0])] = int(p[2])
print(" N | a%8 a%16 | c%8 c%16 | (a-c)/4 %2 | sd-swappable-middle (=c-d) %8 | inner d %8")
for N in range(2, 42):
    s = f"{N:2d} | "
    s += (f"{a[N] % 8:3d} {a[N] % 16:4d}" if N in a else "  ?    ?") + " | "
    s += f"{c[N] % 8:3d} {c[N] % 16:4d} | "
    s += (f"{((a[N] - c[N]) // 4) % 2:6d}    " if N in a else "     ?    ") + " | "
    if N in outer:
        s += f"{outer[N] % 8:6d}{'':24s}| {(c[N] - outer[N]) % 8:3d}"
    print(s)
