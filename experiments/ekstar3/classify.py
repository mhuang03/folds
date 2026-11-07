# classify.py FILES... : classify the residual triples "R N a b c" (canonical a + c <= N + 1) of
# cov.c by shape; prints one line per N and a few examples of the "other" class.
import sys
for fn in sys.argv[1:]:
    rows = [tuple(map(int, l.split()[1:])) for l in open(fn) if l.startswith('R')]
    if not rows: continue
    N = rows[0][0]
    cls = {'top-adj(c=b+1)': 0, 'bot-adj(b=a+1)': 0, 'a<=3': 0, 'a<=6': 0, 'other': 0}
    other = []
    for (_, a, b, c) in rows:
        if c == b + 1: cls['top-adj(c=b+1)'] += 1
        elif b == a + 1: cls['bot-adj(b=a+1)'] += 1
        elif a <= 3: cls['a<=3'] += 1
        elif a <= 6: cls['a<=6'] += 1
        else: cls['other'] += 1; other.append((a, b, c))
    tot = len(rows)
    print('N=%d resid=%d ' % (N, tot) + ' '.join('%s:%d' % kv for kv in cls.items()),
          'other e.g.', other[:6])
