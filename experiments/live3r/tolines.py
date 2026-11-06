# tolines.py FILE: turn resid.py output into lines "N a b c"
import sys, re
for line in open(sys.argv[1]):
    m = re.match(r'N=(\d+)', line)
    if not m: continue
    N = int(m.group(1))
    for t in re.findall(r'\((\d+),(\d+),(\d+)\)', line):
        print(N, *t)
