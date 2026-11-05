"""antipoint.py n1 n2: the anti-point problem AP(n, w): order [n] \\ {w} from scratch on a
background of weight -1 at w, i.e. each step y needs
    #(placed in L(y)) - #(placed in R(y)) = [w in L(y)] - [w in R(y)].
Prints, per n, the w for which this is impossible.  (A residue chain with r+1 in a later
class than r reduces the adjacent pair {r, r+1} to an anti-point problem in that class strip,
for generic k.)"""
import sys
from lib import arms


def ap_ok(n, w, weight=-1):
    T = [x for x in range(1, n + 1) if x != w]
    idx = {x: i for i, x in enumerate(T)}
    m = len(T)
    A = [arms(n, x) for x in T]
    base = [weight * ((w in L) - (w in R)) for (L, R) in A]
    Lm = [sum(1 << idx[z] for z in L if z in idx) for (L, R) in A]
    Rm = [sum(1 << idx[z] for z in R if z in idx) for (L, R) in A]
    reach = bytearray(1 << m)
    reach[0] = 1
    for S in range(1 << m):
        if not reach[S]:
            continue
        for i in range(m):
            if not S >> i & 1:
                if base[i] + bin(S & Lm[i]).count('1') - bin(S & Rm[i]).count('1') == 0:
                    reach[S | 1 << i] = 1
    return bool(reach[(1 << m) - 1])


if __name__ == '__main__':
    wt = int(sys.argv[3]) if len(sys.argv) > 3 else -1
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        print(n, [w for w in range(1, n + 1) if not ap_ok(n, w, wt)])
        sys.stdout.flush()
