"""failset.py file: residues rho that fail for some q in a rec.cpp output, and those that never fail."""
import re, sys
bad = {}
for l in open(sys.argv[1]):
    m = re.match(r'q=(\d+) FAIL rho:(.*)', l)
    if m:
        for x in m.group(2).split():
            bad.setdefault(int(x), []).append(int(m.group(1)))
for r in range(1, 17):
    print(r, 'never fails' if r not in bad else 'fails for %d q, first %d' % (len(bad[r]), bad[r][0]))
