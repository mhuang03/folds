"""summ.py: summarize 'UNC N=.. u=.. u'=..' lines from stdin by (N, u)."""
import sys
import re
from collections import defaultdict
d = defaultdict(list)
for line in sys.stdin:
    m = re.match(r"UNC N=(\d+) u=(\d+) u'=(\d+)", line)
    if m:
        N, u, up = map(int, m.groups())
        d[(N, u)].append(up)
    elif line.startswith('total'):
        print(line.strip())
skip1 = len(sys.argv) > 1
for (N, u), ups in sorted(d.items()):
    if skip1 and u == 1:
        continue
    print(N, u, len(ups), min(ups), max(ups))
