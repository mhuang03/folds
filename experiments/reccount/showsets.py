"""List the proper neutral sets written by decomp (out/sets_N.txt).
usage: python3 showsets.py N [N ...]"""
import sys

for a in sys.argv[1:]:
    n = int(a)
    print(f"N={n}")
    for line in open(f"out/sets_{n}.txt"):
        m, k, g, gi, h = line.split()
        m = int(m, 16)
        el = [x for x in range(1, n + 1) if m >> (x - 1) & 1]
        print("  ", el, "g", g, "gI", gi, "h", h)
