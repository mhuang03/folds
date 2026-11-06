"""Summary table of out/bisim_N.txt and out/trace_N.txt (written into out/summary.txt)."""
import os

lines = []
lines.append('bisim (live sets only; orbits = live mirror orbits)')
lines.append(' N   live/2^N  bisim/orbits(all layers)  max-layer bisim/orbits  middle-layer bisim/orbits  middle fvals/orbits')
for n in range(4, 40):
    fn = 'out/bisim_%d.txt' % n
    if not os.path.exists(fn):
        continue
    rows = [list(map(int, l.split())) for l in open(fn) if l[0] != '#' and not l.startswith('TOTAL')]
    tot = [l for l in open(fn) if l.startswith('TOTAL')][0].split()
    d = {x.split('=')[0]: int(x.split('=')[1]) for x in tot[2:]}
    mo = max(r[3] for r in rows)
    mf = max(r[6] for r in rows)
    mid = rows[n // 2]
    lines.append('%2d   %.3f     %.3f                     %.3f                   %.3f                     %.3f' % (
        n, d['live'] / d['sets'], d['bisimF'] / d['orbits'], mf / mo, mid[6] / mid[3], mid[4] / mid[3]))
lines.append('')
lines.append('traces (sets with g > 0, mirror-identified) at the middle layer h = floor(N/2) and h-1')
lines.append(' N   traces(h)  orbits(h)  ratio   traces(h-1) orbits(h-1) ratio')
for n in range(4, 40):
    fn = 'out/trace_%d.txt' % n
    if not os.path.exists(fn):
        continue
    rows = {int(l.split()[0]): l.split() for l in open(fn) if l[0] != '#' and not l.startswith('TOTAL')}
    h = n // 2
    a = rows.get(h)
    b = rows.get(h - 1)
    if a is None or b is None:
        continue
    lines.append('%2d %10s %10s  %.3f %10s %10s  %.3f' % (n, a[4], a[3], int(a[4]) / int(a[3]), b[4], b[3], int(b[4]) / int(b[3])))
open('out/summary.txt', 'w').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
