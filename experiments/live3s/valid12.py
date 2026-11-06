# which {1, 2, c} are valid and not dead
from base import *
for N in range(20, 80):
    cs = cs12(N)
    rs = []
    for c in cs:
        if rs and rs[-1][1] == c - 1: rs[-1][1] = c
        else: rs.append([c, c])
    print(N, N % 8, ' '.join(f'{a}-{b}' if a != b else str(a) for a, b in rs))
