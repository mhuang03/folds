"""verify.py: rigorous (ball arithmetic) verification of rest2(s, a) < 2 for all s >= 4, a >= 2 with
k = s + a + 1 >= 28  (PROOFS.txt, Theorem 6.1).

  part 1 (m = s + a in [MLO, M1 - 1]):  U(s, a) < 2 for every admissible (s, a)   (ubound.U)
  part 2 (m >= M1):  U(s, a) <= F(m)  (Lemma 6.2: termwise majorants f_i(m), independent of s),
          every term of F is P(m) lam^m with deg P <= 3, lam <= 3/4, hence decreasing for m >= 40,
          and F(M1) < 2.
usage: python3 verify.py [MLO] [M1] [MSHOW]"""
import sys
from math import comb
from flint import arb
from ubound import U, Ua, UI, U0, Vp, G, G2, K, PI, TWO

E16 = arb(16) / 15          # eps_s <= 16/15
ES = arb('1.31')            # eps_s^s <= 1.31  (s >= 4)


def F_terms(m):
    m_ = arb(m)
    t = {}
    t['alpha0'] = 32 * E16 * (arb(3) / 4) ** m
    t['alpha1'] = 237 * TWO ** -m + 54 * TWO ** (-m_ / 2)
    k = m + 1
    t['I'] = PI * G * G2 * (9 * (TWO / 3) ** k + 128 * k * TWO ** -k)
    t['0'] = (2 * PI ** 2 * E16 * G2 / (PI / 32).cos()
              * (G * TWO.sqrt() * PI / 8 * (27 * arb(3) ** -m + m * TWO ** (9 - 2 * m))
                 + arb(3) ** (3 - m) + TWO ** (9 - 2 * m)))
    fa = 47.2 * m ** 2 * TWO ** (arb('6.02') - m)
    s2, s3 = m - 2, m - 3
    # (omega_s / 2)^s = (2/3)^s eps^s <= 1.31 (2/3)^s ;  (omega_s/4)^s <= 1.31 (1/3)^s
    b2 = 47.2 * s2 * ES * (arb(2) / 3) ** s2 * (3 + comb(m, 2))
    b3 = 47.2 * s3 * ES * (arb(1) / 3) ** s3 * (4 + arb(comb(m, 3)) / 2)
    b4 = 47.2 * m * (m + 5) * (arb(16) / 45) ** (m_ / 2 + 1)
    c2 = G * ((arb(2) / 3) ** s2 + 8 * K * ES * TWO ** -s2) * (8 * E16 + arb(comb(m, 2)) / 2)
    c3 = arb('10.3') * G * ES * arb(4) ** -s3 * (E16 * TWO ** (m + 1)
                                                + comb(m, 3) * (TWO ** (s3 - 3) + 3))
    c4 = arb('10.3') * G * (arb('1.40') * TWO ** (13 - 2 * m) + ES * TWO ** (8 - m) * (1 + m_ / 16))
    t['IIa'] = PI * G * fa
    t['IIb'] = PI * G * (b2 + b3 + b4)
    t['IIc'] = PI * G * (c2 + c3 + c4)
    return t


def F(m):
    return sum(F_terms(m).values())


if __name__ == '__main__':
    MLO = int(sys.argv[1]) if len(sys.argv) > 1 else 27
    M1 = int(sys.argv[2]) if len(sys.argv) > 2 else 41
    MSHOW = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    print(f'G = {G.str(8)}, G2 = {G2.str(8)}, K = {K.str(8)}')
    ok = True
    for m in range(MLO, M1):
        worst = (arb(0), None)
        for s in range(4, m - 1):
            a = m - s
            u = U(s, a)
            if not (u < 2):
                ok = False
                print(f'  FAIL at (s,a)=({s},{a}): U = {u.str(6)}')
            if u.upper() > worst[0].upper():
                worst = (u, (s, a))
        print(f'm={m} (k={m + 1}): max_s U(s,a) = {worst[0].str(5, radius=False)} '
              f'(upper {float(worst[0].upper()):.5g}) at (s,a)={worst[1]}', flush=True)
    for m in range(M1, MSHOW + 1):
        f = F(m)
        if m == M1:
            ok = ok and bool(f < 2)
            print(f'F({M1}) = {f.str(6, radius=False)} (upper {float(f.upper()):.5g})  terms:',
                  {kk: v.str(3, radius=False) for kk, v in F_terms(m).items()})
        else:
            print(f'F({m}) = {float(f.upper()):.4g}')
    print('VERIFIED' if ok else 'NOT VERIFIED')
