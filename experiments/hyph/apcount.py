"""apcount.py file q: counts of AP middle sets per difference d (from apmid output)."""
import re, sys, collections
q = int(sys.argv[2])
for line in open(sys.argv[1]):
    nu, rest = line.split(':')
    c = collections.Counter()
    for k, d, a in re.findall(r'\((\d+),(\d+),(\d+)\)', rest):
        c[int(d)] += 1
    print(q, nu, dict(sorted(c.items())))
