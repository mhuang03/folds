# coverage8.py C S X1 X2 ...: like ../superexp7/coverage2.py (fraction of random N in [X, 2X]
# for which some M = 2^j >= sqrt(N)/C and some q in (N/(M+1), N/M] have a PROVEN H(q, N - qM)),
# comparing the superexp7 set of proven pairs with the set enlarged by SuperExp8
# (SmallRes: rho in {0,1,2,4,q-1,q-2,q-4}, and rho in {3, q-3} for even q, closed under block
# composition), and with the hypothetical set "every rho <= 8 (and mirror), every q".
import sys, math, random
from functools import lru_cache
sys.setrecursionlimit(10000)
sys.path.insert(0, '../superexp7')
from coverage_lib import H as H7, smooth, divisors


def small8(q, r):
    return r in (0, 1, 2, 4) or r in (q - 1, q - 2, q - 4) or (q % 2 == 0 and r in (3, q - 3))


@lru_cache(maxsize=None)
def H8(q, r):
    if r == 0 or (q >= 2 and r in (1, q - 1)) or smooth(q) or small8(q, r):
        return True
    for d in divisors(q):
        for (m, j) in ((q // d, d), (d, q // d)):
            c, e = divmod(r, j)
            if H8(j, e) and H8(m, c) and (e == 0 or H8(m, (c + 1) % m)):
                return True
    return False


@lru_cache(maxsize=None)
def Hhyp(q, r):
    if r <= 8 or r >= q - 8 or smooth(q):
        return True
    for d in divisors(q):
        for (m, j) in ((q // d, d), (d, q // d)):
            c, e = divmod(r, j)
            if Hhyp(j, e) and Hhyp(m, c) and (e == 0 or Hhyp(m, (c + 1) % m)):
                return True
    return False


C = float(sys.argv[1]); S = int(sys.argv[2])
random.seed(1)
for X in (int(float(a)) for a in sys.argv[3:]):
    cnt = [0, 0, 0]
    for _ in range(S):
        N = random.randrange(X, 2 * X)
        for idx, H in enumerate((H7, H8, Hhyp)):
            found = False; M = 1
            while M * (M + 1) <= N and not found:
                if M >= math.sqrt(N) / C:
                    for q in range(N // (M + 1) + 1, N // M + 1):
                        r = N - q * M
                        if 0 <= r < q and H(q, r):
                            found = True; break
                M *= 2
            cnt[idx] += found
    print(f"X={X:.1e} C={C}: covered superexp7 {cnt[0]}/{S}, +SmallRes {cnt[1]}/{S}, "
          f"all rho<=8 {cnt[2]}/{S}", flush=True)
