# endstep.py NMAX: among the valid, non-dead 3-sets that fail the closed-form Theorem G
# criterion F3S, count those for which B u E satisfies Theorem G for E = {1}, {N}, {1, N}
# (panels 1 and N have reach 0, so they are always valid steps: coReach_of_step), and list
# a few that remain.
import sys
from inward3 import imb, inward_any, Fsym

def valid_sets(N):
    S = set()
    for x in range(1, N + 1):
        for y in range(1, N + 1):
            if y == x or imb(N, {x}, y): continue
            for z in range(1, N + 1):
                if z in (x, y) or imb(N, {x, y}, z): continue
                S.add(tuple(sorted((x, y, z))))
    return S

def dead(N, a, b, c):
    for j in range(2, (N + 3) // 4 + 1):
        if (a, b, c) == (1, 2 * j, 2 * j + 1) or (a, b, c) == (N - 2 * j, N + 1 - 2 * j, N):
            return True
    return N % 2 == 1 and N >= 7 and {a, b, c} <= {1, 2, N - 1, N}

if __name__ == '__main__':
    for N in range(8, int(sys.argv[1]) + 1):
        rest = [t for t in valid_sets(N) if not dead(N, *t) and not Fsym(N, *t)]
        cnt = {'1': 0, 'N': 0, '1N': 0, 'none': 0}
        left = []
        for t in rest:
            B = set(t)
            ok = False
            for name, E in (('1', {1}), ('N', {N}), ('1N', {1, N})):
                if E & B and name != '1N': continue
                if inward_any(N, B | E):
                    cnt[name] += 1; ok = True; break
            if not ok:
                cnt['none'] += 1; left.append(t)
        print(N, len(rest), cnt, sorted(left)[:12])
