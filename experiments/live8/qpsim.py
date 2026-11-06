"""qpsim.py N [C]: simulate the deterministic (Q,P) sliding-window construction for the combo
Z, orientation 0 (K = N + 2, L = u, R = u', alpha = 0, beta = 1, s = q in [2, K // 2]).
For every wide mixed pair: Dirichlet Q1 <= Q0 (best), multiple k, j chosen to center, Delta,
s-range, and the position-free union test.  Reports the uncovered pairs (u, u') and the minimum
of u * (K - 2u')^3 / K^3 over them."""
import sys
from math import gcd, isqrt


def windows_ok(K, L, R, Q, P, j, Delta, s1, s2):
    """check the sliding-window hypotheses; return True if a witness is guaranteed"""
    al, be = 0, 1
    E = Q * R - P * L
    C = Q * be - P * al
    if s1 > s2 or s1 < 2 or s2 > K // 2:
        return False
    for s in (s1, s2):
        D = j * K - s * E - C
        if abs(D) > Delta:
            return False
    def h(s):
        return min(s - 1, (Q * (s - 1) - Delta) // P)
    if h(s1) - Delta + 1 < L:
        return False
    union = (s2 - s1) * L + h(s2) - Delta + 1
    return union >= Q * K


def try_pair(N, u, up, verbose=False):
    K, L, R = N + 2, u, up
    smax = K // 2
    best = None
    # Dirichlet over Q1 <= Q0 for several Q0
    for Q1 in range(1, 2 * isqrt(K) + 2):
        P1 = (Q1 * R + L // 2) // L
        if P1 < 1:
            continue
        E1 = Q1 * R - P1 * L
        for k in range(1, 200):
            Q, P = k * Q1, k * P1
            E = k * E1
            if Q * K > smax * L:
                break
            # choose Delta and j: try a few Delta
            for frac in (2, 3, 4, 6, 8, 12, 16):
                Delta = (smax - R) // frac
                if Delta < 0:
                    continue
                if E == 0:
                    j = (Q + K // 2) // K  # D = jK - Q, j = 0 normally
                    # s range: contiguity from below, smax above
                    s2 = smax
                    s1 = R
                    while s1 <= s2 and min(s1 - 1, (Q * (s1 - 1) - Delta) // P) - Delta + 1 < L:
                        s1 += 1
                    if windows_ok(K, L, R, Q, P, j, Delta, s1, s2):
                        return (Q, P, j, Delta, s1, s2)
                    continue
                # s0 = (jK - C)/E; choose j so that s0 + Delta/|E| <= smax, maximal
                C = Q
                w = Delta // abs(E)
                # want s2 = s0 + w <= smax
                if E > 0:
                    j = ((smax - w) * E + C) // K
                else:
                    j = -((-(smax - w) * E - C) // K) if False else ((smax - w) * E + C) // K
                for jj in (j - 1, j, j + 1):
                    # s range where |jj K - s E - C| <= Delta
                    if E > 0:
                        s1 = -((-(jj * K - C - Delta)) // E)
                        s2 = (jj * K - C + Delta) // E
                    else:
                        s1 = -((-(jj * K - C + Delta)) // E)
                        s2 = (jj * K - C - Delta) // E
                    s2 = min(s2, smax)
                    while s1 <= s2 and min(s1 - 1, (Q * (s1 - 1) - Delta) // P) - Delta + 1 < L:
                        s1 += 1
                    if windows_ok(K, L, R, Q, P, jj, Delta, s1, s2):
                        return (Q, P, jj, Delta, s1, s2)
    return None


if __name__ == '__main__':
    N = int(sys.argv[1])
    K = N + 2
    unc = []
    tot = 0
    for u in range(1, N):
        for up in range(u, N):
            if u + 2 * up > N - 1:
                break
            v = N + 1 - up
            if (u + v) % 2 == 0:
                continue
            tot += 1
            if try_pair(N, u, up) is None:
                unc.append((u, up))
    print('total', tot, 'uncovered', len(unc))
    if unc:
        m = min(u * (K - 2 * up) ** 3 / K ** 3 for u, up in unc)
        mx = max(u * (K - 2 * up) ** 3 / K ** 3 for u, up in unc)
        print('min/max of u (K-2u\')^3/K^3 over uncovered: %.3f %.3f' % (m, mx))
        # profile: for each u, max (K - 2u') among uncovered
        prof = {}
        for u, up in unc:
            prof[u] = max(prof.get(u, 0), K - 2 * up)
        print(sorted(prof.items())[:: max(1, len(prof) // 40)])
