"""Family 5: number-theoretic structure.

(1) Berlekamp-Massey over F_p for every prime p <= 97, for a(1..37), a(k..37) (k <= 8)
    and c(1..41).  A random sequence of length n has linear complexity ~ n/2; a genuine
    recurrence of order L is only *verified* if n >= 2L + 5 (then BM's answer is forced
    by 5 extra terms).
(2) Ultimate periodicity mod m, m <= 64: smallest preperiod t <= 10, period P with
    P + t <= (37 - 5)/2 (so at least 5 extra checks beyond one full period... need
    a(n+P) == a(n) for all t <= n <= 37 - P, and 37 - P - t + 1 >= P + 5).
(3) p-adic valuations v_p(a(N)) for p = 2, 3, 5, 7, frequency of p | a(N) vs 1/p.
(4) Lucas-type congruences a(pn + k) == a(n) a(k) (mod p), a(0) = 1.
"""
from common import A, C, NMAX


def primes(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def bm(s, p):
    """Berlekamp-Massey over F_p. Returns (L, connection polynomial)."""
    Cp, Bp = [1], [1]
    L, m, b = 0, 1, 1
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            d = (d + Cp[i] * s[n - i]) % p
        if d == 0:
            m += 1
            continue
        coef = d * pow(b, -1, p) % p
        T = Cp[:]
        if len(Cp) < len(Bp) + m:
            Cp += [0] * (len(Bp) + m - len(Cp))
        for i, x in enumerate(Bp):
            Cp[i + m] = (Cp[i + m] - coef * x) % p
        if 2 * L <= n:
            L, Bp, b, m = n + 1 - L, T, d, 1
        else:
            m += 1
    return L, Cp


def vp(x, p):
    if x == 0:
        return None
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def main():
    print(__doc__)
    a = [A[n] for n in range(1, NMAX + 1)]
    c = [C[n] for n in range(1, len(C))]
    print('(1) Berlekamp-Massey linear complexity L over F_p  (n terms; verified iff n >= 2L+5)')
    print('    p : L(a 1..37)  min_k L(a k..37), k<=8  L(c 1..41)  L(c(2n), n<=20)')
    sig = []
    c2 = [C[2 * n] for n in range(1, 21)]
    for p in primes(97):
        La = bm([x % p for x in a], p)[0]
        Lk = min((bm([x % p for x in a[k - 1:]], p)[0], k) for k in range(1, 9))
        Lc = bm([x % p for x in c], p)[0]
        Lc2 = bm([x % p for x in c2], p)[0]
        flag = ''
        if 37 >= 2 * La + 5:
            flag += ' a-VERIFIED'
        if 37 - Lk[1] + 1 >= 2 * Lk[0] + 5:
            flag += ' tail-VERIFIED'
        if 41 >= 2 * Lc + 5:
            flag += ' c-VERIFIED'
        if 20 >= 2 * Lc2 + 5:
            flag += ' c2-VERIFIED'
        print(f'   {p:2d} : {La:3d}  {Lk[0]:3d} (k={Lk[1]})  {Lc:3d}  {Lc2:3d}{flag}')
        if flag:
            sig.append((p, flag))
    print('   verified short recurrences:', sig if sig else 'none')

    print('\n(2) ultimate periodicity of a(N) mod m, m = 2..64 (with >= 5 extra checks)')
    hits = []
    for m in range(2, 65):
        r = [x % m for x in a]
        found = None
        for P in range(1, 37):
            for t in range(0, 10):
                checks = len(r) - P - t
                if checks < P + 5:
                    continue
                if all(r[n + P] == r[n] for n in range(t, len(r) - P)):
                    found = (t + 1, P)
                    break
            if found:
                break
        if found:
            hits.append((m, found))
    print('   periodic moduli (m, (start N, period)):', hits if hits else 'none')
    print('   (a(N) mod 2 = 0 for N >= 2 is the trivial hit if listed)')

    print('\n(3) p-adic valuations v_p(a(N)), N = 1..37')
    for p in (2, 3, 5, 7, 11, 13):
        v = [vp(x, p) for x in a]
        frac = sum(1 for x in v if x > 0) / len(v)
        print(f'   p={p:2d}: {v}   share divisible {frac:.2f} (random 1/p = {1 / p:.2f})')

    print('\n(4) Lucas-type test a(pn+k) == a(n) a(k) (mod p), a(0)=1')
    full = [1] + a
    for p in (3, 5, 7, 11, 13):
        tot = ok = 0
        for N in range(p, NMAX + 1):
            n, k = divmod(N, p)
            tot += 1
            ok += (full[N] - full[n] * full[k]) % p == 0
        print(f'   p={p:2d}: holds for {ok}/{tot} N  (chance ~ {tot / p:.1f})')


if __name__ == '__main__':
    main()
