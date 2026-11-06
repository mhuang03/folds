# collect.py FILES...: merge resid.py outputs into resid.txt form (one line per N, sorted,
# the later file wins), dropping the r= field of the first runs, and print a summary of the
# triples that are not of the form {1, 2, c}.
import sys, re
rows = {}
for fn in sys.argv[1:]:
    for line in open(fn):
        m = re.match(r'N=(\d+) q=(\d+)(?: r=\d+)? T:(.*)', line.strip())
        if m: rows[int(m.group(1))] = (int(m.group(2)), m.group(3).split())
for N in sorted(rows):
    q, T = rows[N]
    print('N=%d q=%d T: %s' % (N, q, ' '.join(T)))
other = [(N, t) for N in sorted(rows) for t in rows[N][1] if not t.startswith('1,2,')]
print('# not {1,2,c}:', ' '.join('N=%d:%s' % x for x in other))
