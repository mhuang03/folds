"""clregtune.py FILE NMIN NMAX : try line offsets for the cluster regions on N in [NMIN, NMAX]:
A: 50 d + 31 r >= aA, B: 10 d + 13 r + bB <= 0, D/C split at d + r <= cD (D) / >= cD + 1 (C).
Prints the minimal widths per region for each choice."""
import sys
import itertools

nmin, nmax = int(sys.argv[2]), int(sys.argv[3])
rows = []
for line in open(sys.argv[1]):
    a = line.split()
    N, r, d = int(a[0]), int(a[1]), int(a[2])
    if nmin <= N <= nmax:
        rows.append((r, d, [float(x) for x in a[4:8]]))
best = []
for aA, bB, cD in itertools.product(range(500, 900, 25), range(70, 200, 10), range(-3, 2)):
    m = {'A': 9, 'B': 9, 'C': 9, 'D': 9}
    for r, d, ws in rows:
        A = 50 * d + 31 * r >= aA
        B = 10 * d + 13 * r + bB <= 0
        if A:
            m['A'] = min(m['A'], ws[0])
        if B:
            m['B'] = min(m['B'], ws[1])
        if not A and not B:
            if d + r <= cD:
                m['D'] = min(m['D'], ws[3])
            else:
                m['C'] = min(m['C'], ws[2])
    best.append((min(m.values()), aA, bB, cD, m))
best.sort(key=lambda t: -t[0])
for b in best[:10]:
    print(b)
