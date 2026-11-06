"""Pre = the panels before the first panel u of the other parity.  The gaps = maximal runs
of consecutive values in [1,N] avoiding Pre.  Report the maximal gap length, the maximal
end-gap lengths, and how many gaps of length 3 occur."""
import sys
from collections import Counter
from apfree import enum

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for N in range(3, Nmax + 1):
    L = enum(N)
    stats = Counter()
    maxgap = 0
    maxend = 0
    for w in L:
        i = next(t for t in range(N) if w[t] % 2 != w[0] % 2)
        pre = set(w[:i])
        gaps = []
        run = 0
        for x in range(1, N + 2):
            if x <= N and x not in pre:
                run += 1
            else:
                gaps.append(run); run = 0
        maxgap = max(maxgap, max(gaps))
        maxend = max(maxend, gaps[0], gaps[-1])
        stats[tuple(sorted(Counter(gaps).items()))] += 0
        stats[('n3', gaps.count(3), 'p', i)] += 1
    print(f'N={N:2d} max gap {maxgap}, max end gap {maxend};',
          sorted((k, v) for k, v in stats.items() if v and k[0] == 'n3'))
