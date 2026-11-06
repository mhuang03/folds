"""Compare log10|b1| for a(N) with the size-matched negative control in lll_out.txt."""
txt = open('lll_out.txt').read()
body = txt.split('\na(N), N <= 37')[1]
a_part, c_part, c2_part = body.split('negative control')


def parse(t):
    d = {}
    for line in t.splitlines():
        f = line.split()
        if len(f) >= 6 and f[0].isdigit() and f[4] == 'yes':
            d[(int(f[0]), int(f[1]))] = float(f[5])
    return d


a = parse(a_part)
c = parse(c_part)
c2 = parse(c2_part)
keys = sorted(k for k in a if k in c)
print('box (r,d), K, log10|b1| for a(N), control 10% noise, control 1% noise, a - control(1%)')
for k in keys:
    print(f'  {k}  K={(k[0] + 1) * (k[1] + 1):3d}  {a[k]:6.1f}  {c[k]:6.1f}  {c2[k]:6.1f}  {a[k] - c2[k]:+5.1f}')
d2 = [a[k] - c2[k] for k in keys]
print(f'vs 1% control: mean difference {sum(d2) / len(d2):+.2f}, min {min(d2):+.1f}, max {max(d2):+.1f}')
diffs = [a[k] - c[k] for k in keys]
print(f'vs 10% control: {len(diffs)} boxes; mean difference {sum(diffs) / len(diffs):+.2f}, min {min(diffs):+.1f}, max {max(diffs):+.1f}')
print('min log10|b1| for a(N) over all underdetermined boxes:', min(a.values()))
