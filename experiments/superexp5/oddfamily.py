"""The odd-node family (PROOFS.txt, Theorem F), built explicitly.

N = 2n+1, slips only at k = 2i, i in U ⊆ I(n):
  n = 2p+1 (odd child = first block):  I = {i >= 1 : 2i <= p, i = p (mod 2)}
      tau = PB(alpha, beta), alpha in V_{p+1} free, beta in V_p with  i before 2i,
      sigma in V_{n+1} with  4i+1 before 2i+1          (i in U)
  n = 2p   (odd child = second block): I = {i >= 1 : 2i <= p, i = p+1 (mod 2)}
      tau in V_n with  2i before 4i,
      sigma = PB(alpha', beta'), alpha' in V_{p+1} with 2i+1 before i+1, beta' in V_p free.
Checks: every member valid, all distinct, number = sum_U (product of the three counts),
and the averaging ratio 4 W / (a a 2^{ceil(|I|/4)}) >= 1.
usage: python3 oddfamily.py Nmax [stride]
"""
import sys
from math import ceil
from oddslip import V, valid_seq, subsets


def PB(a, b): return tuple([2 * x - 1 for x in a] + [2 * y for y in b])


def bef(t, x, y): return t.index(x) < t.index(y)


def main():
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    cache = {}

    def VV(m):
        if m not in cache:
            cache[m] = V(m)
        return cache[m]
    for N in range(5, Nmax + 1, 2):
        n = N // 2
        p = n // 2
        if n % 2:
            I = [i for i in range(1, p + 1) if 2 * i <= p and (i - p) % 2 == 0]
        else:
            I = [i for i in range(1, p + 1) if 2 * i <= p and (i - p - 1) % 2 == 0]
        seen = set()
        count = formula = 0
        bad = 0
        W = 0
        idx = 0
        for U in subsets(I):
            D = {2 * i for i in U}
            f = [0] + [2 * i + (1 if i in D else 0) for i in range(1, n + 1)]
            g = [0] + [2 * i - 1 - (1 if (i - 1) in D else 0) for i in range(1, n + 2)]
            if n % 2:
                As = VV(p + 1)
                Bs = [b for b in VV(p) if all(bef(b, i, 2 * i) for i in U)]
                Ss = [s for s in VV(n + 1) if all(bef(s, 4 * i + 1, 2 * i + 1) for i in U)]
                taus = [PB(a, b) for a in As for b in Bs]
                sigs = Ss
                W += len(Bs) * len(Ss)
            else:
                Ts = [t for t in VV(n) if all(bef(t, 2 * i, 4 * i) for i in U)]
                A2 = [a for a in VV(p + 1) if all(bef(a, 2 * i + 1, i + 1) for i in U)]
                B2 = VV(p)
                taus = Ts
                sigs = [PB(a, b) for a in A2 for b in B2]
                W += len(Ts) * len(A2)
            formula += len(taus) * len(sigs)
            for t in taus:
                for s in sigs:
                    idx += 1
                    seq = tuple([f[i] for i in t] + [g[i] for i in s])
                    count += 1
                    seen.add(seq)
                    if idx % stride == 0 and not valid_seq(seq, N):
                        bad += 1
        if n % 2:
            base = len(VV(p)) * len(VV(n + 1))
        else:
            base = len(VV(n)) * len(VV(p + 1))
        ratio = 4 * W / (base * 2 ** ceil(len(I) / 4))
        print(f"N={N} n={n} |I|={len(I)} members={count} distinct={len(seen)} "
              f"formula={formula} invalid(checked every {stride})={bad} 4W/(aa2^c)={ratio:.3f}",
              flush=True)


if __name__ == "__main__":
    main()
