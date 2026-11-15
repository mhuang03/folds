"""Reads out/<mode>_N.txt (from xd) and prints the tables used in NOTES.txt."""
import sys, os
from fractions import Fraction
from common import A

def load(mode, N):
    fn = os.path.join(os.path.dirname(__file__), "out", "%s_%d.txt" % (mode, N))
    d = {"pos": {}}
    for line in open(fn):
        w = line.split()
        if w[0] == "pos": d["pos"][int(w[1])] = [int(x) for x in w[2:]]
        elif w[0] == "N": pass
        elif w[0] in ("total", "signed"): d[w[0]] = int(w[1])
        else: d[w[0]] = [int(x) for x in w[1:]]
    return d

def v(p, x):
    if x == 0: return None
    k = 0
    while x % p == 0: x //= p; k += 1
    return k

if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    print("== signed count D(N) and #even = (a+D)/2")
    for N in range(1, Nmax + 1):
        d = load("semi", N); assert d["total"] == A[N]
        print(N, d["signed"], (A[N] + d["signed"]) // 2)
    print("== time rank of panel 1: E(N,k) = #valid sequences with panel 1 at step k")
    for N in range(2, min(Nmax, 16) + 1):
        d = load("semi", N); print(N, d["pos"][1])
    print("== mean step of panel m, minus (N+1)/2 is 0 by reversal; variance of t_m / ((N^2-1)/12)")
    for N in (8, 12, 16, 20, 24):
        if N > Nmax: break
        d = load("semi", N); row = []
        for m in range(1, N // 2 + 1):
            p = d["pos"][m]; mu = Fraction(N + 1, 2)
            var = sum(Fraction(c) * (k + 1 - mu) ** 2 for k, c in enumerate(p)) / A[N]
            row.append("%.3f" % float(var / Fraction(N * N - 1, 12)))
        print(N, " ".join(row))
    print("== parity of the step of panel m: #(t_m odd) - #(t_m even)")
    for N in range(2, min(Nmax, 16) + 1):
        d = load("semi", N)
        print(N, [sum(c if k % 2 == 0 else -c for k, c in enumerate(d["pos"][m])) for m in range(1, (N + 1) // 2 + 1)])
    print("== expected number of valid moves after k steps along a uniform valid sequence: M(k)/a(N)")
    for N in range(4, Nmax + 1, 4):
        d = load("semi", N)
        print(N, " ".join("%.3f" % (m / A[N]) for m in d["moves"]))
    print("== sum_k M(k)/a(N)  (total branching seen by a valid sequence), and /N")
    for N in range(2, Nmax + 1):
        d = load("semi", N); s = sum(d["moves"])
        print(N, s, "%.4f" % (s / A[N]), "%.4f" % (s / A[N] / N))
    print("== dead ends: #dead sets per layer / #dead prefixes total / T(N,k)")
    for N in range(4, Nmax + 1):
        d = load("semi", N)
        print(N, "deadsets", sum(d["deadsets"]), "deadprefixes", sum(d["deadprefixes"]),
              "sumT", sum(d["T"]), "odd-layer deadsets", sum(d["deadsets"][1::2]))
    print("== 2-adic and 3-adic valuations: a(N), a(N)/2, F(N,m)")
    for N in range(2, Nmax + 1):
        d = load("semi", N)
        F = [d["pos"][m][0] for m in range(1, (N + 1) // 2 + 1)]
        print(N, "v2(a)", v(2, A[N]), "v3(a)", v(3, A[N]), "v2(F)", [v(2, f) for f in F], "v3(F)", [v(3, f) for f in F])
    print("== deletion-compatible counts and relaxations")
    for N in range(2, min(Nmax, 22) + 1):
        row = [N, A[N]]
        for mode in ("del1", "delN1", "delmid", "left", "leftx"):
            row.append(load(mode, N)["total"])
        print(*row)
