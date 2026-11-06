# {1, 2, c} not settled by the closed-form near copies
#   O  : phi12 into N = 2p - 1, p odd (Live3r coReach_one_two_odd), c odd, 7 <= c <= N - 4
#   F1 : phi12 into N = 2p, c odd, 5 <= c, preimage {1, 2, (c+1)/2} not dead in [p]
#   F2 : phiE  into N = 2p + 1, p odd, c even, 6 <= c <= N - 5
import sys
from base import *

def dead_p(p, g):  # {1, 2, g} dead in [p]
    return dead3(p, 1, 2, g)

def fam(N, c):
    if N % 4 == 1 and c % 2 == 1 and 7 <= c <= N - 4: return 'O'
    if N % 2 == 0 and c % 2 == 1 and c >= 5 and not dead_p(N // 2, (c + 1) // 2): return 'F1'
    if N % 4 == 3 and c % 2 == 0 and 6 <= c <= N - 5: return 'F2'
    return None

if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        left = [c for c in cs12(N) if fam(N, c) is None]
        print(N, N % 8, left)
