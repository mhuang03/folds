"""proven_cover.py N1 N2: which reachable 2-sets {u,v} are shown live by the proven transfer
lemmas alone (recursively), and which need more.
  P  parity transfer        u = v (mod 2): class world, pair ((u+c)/2, (v+c)/2)
  SX shifted blocks, N = 2n  u, v in X = {2y + [y > n/2]} : (n-1)-world
  T3 mod-3 split, N = 3n     u, v = 2 (mod 3): n-world;  u, v != 2 (mod 3): 2n-world
  C  (option 'comp') composition: q | N, u = v (mod q): class world N/q
  M  mirror
Liveness of a 2-set only depends on the set (extends_iff_g_pos).  Base: N <= 3 all live."""
import sys
from functools import lru_cache


def reachable(N, u, v):
    if u > v:
        u, v = v, u
    return 2 * v >= N + u + 1 or 2 * u <= v


@lru_cache(None)
def proven(N, u, v):
    if u > v:
        u, v = v, u
    if N <= 3:
        return True
    # parity
    if (u - v) % 2 == 0:
        c = u % 2
        n1 = (N + c) // 2
        if proven(n1, (u + c) // 2, (v + c) // 2):
            return True
    # shifted X, N = 2n
    if N % 2 == 0 and N >= 4:
        n = N // 2
        inv = {2 * y + (1 if y > n // 2 else 0): y for y in range(1, n)}
        if u in inv and v in inv and n - 1 >= 2 and proven(n - 1, inv[u], inv[v]):
            return True
    # mod 3
    if N % 3 == 0:
        n = N // 3
        if u % 3 == 2 and v % 3 == 2 and n >= 2 and proven(n, (u + 1) // 3, (v + 1) // 3):
            return True
        tt = {y + y // 2: y for y in range(1, 2 * n + 1)}
        if u in tt and v in tt and proven(2 * n, tt[u], tt[v]):
            return True
    # composition: residue classes mod q, q | N, class world n = N/q
    if COMP:
        for q in range(3, N + 1):
            if N % q == 0 and (u - v) % q == 0:
                n = N // q
                s = (u - 1) % q + 1
                if n >= 2 and proven(n, (u - s) // q + 1, (v - s) // q + 1):
                    return True
    # mirror (only try once: canonical form)
    mu, mv = N + 1 - v, N + 1 - u
    if (mu, mv) < (u, v):
        return proven(N, mu, mv)
    return False


COMP = 'comp' in sys.argv[3:]
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    tot = ok = 0
    miss = []
    for u in range(1, N + 1):
        for v in range(u + 1, N + 1):
            if not reachable(N, u, v):
                continue
            if (u, v) == (1, N) and (N % 2 == 0 or N == 7):
                continue
            tot += 1
            if proven(N, u, v):
                ok += 1
            else:
                miss.append((u, v))
    print(N, "live pairs", tot, "proven", ok, "missing", len(miss),
          "same-parity missing", sum(1 for u, v in miss if (u - v) % 2 == 0))
