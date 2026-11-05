"""log a_W(N) exactly (lgamma) and its asymptotic expansion.

w(r) = (2r)!!/(2r+1)!! = sqrt(pi) Gamma(r+1) / (2 Gamma(r+3/2)).
Product over r = 0..n-1 via Barnes G:  sum_{r<n} log w(r) = n log(sqrt(pi)/2) + log G(n+1) - log G(n+3/2) + log G(3/2).
"""
from math import lgamma, log, pi
import mpmath as mp

A = [1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
     47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
     2505681033958, 18168130281086, 119006527671252, 979730153850974,
     6564449510287388, 55581983250573500, 413109755332919448, 3603074636066234798,
     27545080998591561856, 262878496654501774250, 2037247307316034896720,
     20222490725552617395966, 171668579369815966705184]


def logw(r):
    return r * log(4) + 2 * lgamma(r + 1) - lgamma(2 * r + 2)


def log_aW(N):
    return lgamma(N + 1) + sum(logw(min(m - 1, N - m)) for m in range(1, N + 1))


def log_aW_mp(N):
    mp.mp.dps = 40
    n = N // 2
    S = n * mp.log(mp.sqrt(mp.pi) / 2) + mp.log(mp.barnesg(n + 1)) - mp.log(mp.barnesg(n + mp.mpf(3) / 2)) + mp.log(mp.barnesg(mp.mpf(3) / 2))
    tot = mp.loggamma(N + 1) + 2 * S
    if N % 2:
        r = n
        tot += r * mp.log(4) + 2 * mp.loggamma(r + 1) - mp.loggamma(2 * r + 2)
    return tot


if __name__ == "__main__":
    mp.mp.dps = 40
    for N in (10, 11, 33):
        print(N, log_aW(N), log_aW_mp(N))
    # asymptotic: log aW = (N/2) log(pi N/(2e)) + beta log N + gamma_parity + O(1/N)
    for par in (0, 1):
        for N in (10**3 + par, 10**4 + par, 10**5 + par, 10**6 + par):
            v = log_aW_mp(N) - mp.mpf(N) / 2 * mp.log(mp.pi * N / (2 * mp.e))
            print("parity", par, N, mp.nstr(v, 15), " minus 1/4 log N:", mp.nstr(v - mp.log(N) / 4, 15),
                  " minus -1/4 log N:", mp.nstr(v + mp.log(N) / 4, 15))
