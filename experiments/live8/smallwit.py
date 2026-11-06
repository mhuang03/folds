"""smallwit.py: witnesses (orient, fam, p, a, b) of the small families for a range of N."""
import sys
from wit8 import witnesses

fams = {
    '(2,N-2)': lambda N: (2, N - 2) if N % 2 == 1 else None,
    '(3,N-3)': lambda N: (3, N - 3) if N % 2 == 1 else None,
    '(3,N-4)': lambda N: (3, N - 4) if N % 2 == 0 else None,
    '(3,N-7)': lambda N: (3, N - 7) if N % 2 == 0 else None,
    '(3,N+1-(N-1)/3)': lambda N: (3, N + 1 - (N - 1) // 3) if N % 3 == 1 and (3 + N + 1 - (N - 1) // 3) % 2 == 1 else None,
    '(3,(N+6)/2)': lambda N: (3, (N + 6) // 2) if N % 4 == 2 else None,
}
for name, f in fams.items():
    print('==', name)
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        pr = f(N)
        if pr is None:
            continue
        u, v = pr
        w = witnesses(N, u, v)
        print(N, N % 12, [x for x in w if x[2] >= 0][:6])
