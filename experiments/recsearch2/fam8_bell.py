"""Family 8 (priority from the literature notes): Bell-type equations, split by parity.

Base series S (exact rationals to x^38), a(0) = 1:
   A      = sum a(n) x^n/n!           (EGF)
   A_ev   = (A(x)+A(-x))/2,  A_od = (A(x)-A(-x))/2       (F(z) +- F(-z))
   B_ev   = sum a(2m) x^m/m!,  B_od = sum a(2m+1) x^m/m!  (EGFs of the parity subsequences)
   and the OGF analogues F, F_ev, F_od, Fe = sum a(2m)x^m, Fo = sum a(2m+1)x^m for (B3).
Coefficient spaces V(c, dz, ke) = span{ z^j e^{k c z} : j <= dz, k <= ke }.
 B1  first order, exponential coefficients:
        S' = sum_{i<=p} G_i(z) theta^i S  [+ H(z)],   G_i, H in V(c, dz, ke)
     (p = 0 is F' = G F, G in Q[z, e^{cz}], i.e. a(n+1) = sum_k C(n,k) c^{n-k} P(k) a(k)-type;
      p >= 1 gives the polynomial weights P(k) in a(k)).
 B2  second order:   S'' = G_1 S' + G_0 S [+ H],  G_i, H in V(c, dz, ke)
 B2' algebraic ODE of order 2 with exponential coefficients: all monomials of degree <= 2
     in S, S', S'' times V(c, 0, ke)
 B3  OGF substitution:   P(x) F(x) = Q(x) F(x/(1-cx)) [+ R(x)],  deg P, Q, R <= d
     and the second-order version with F(x/(1-2cx)) as well.
 c ranges over {1, -1, 2, -2, 1/2, -1/2, 3, -3, 1/3}.  Homogeneous in the unknowns; every box
 has E - K >= 5 (E = number of non-zero coefficient rows that are fully known).
 Control: the Bell numbers (F' = e^z F) and Bessel-type a(n+1) = sum C(n,k) 2^{n-k} (k+1) a(k)
 are found (printed at the end)."""
import itertools, sys
from fractions import Fraction
from math import factorial, comb
from common2 import A, NMAX, analyze

CS = [Fraction(1), Fraction(-1), Fraction(2), Fraction(-2), Fraction(1, 2), Fraction(-1, 2),
      Fraction(3), Fraction(-3), Fraction(1, 3)]


def mul(s, t, L):
    L = min(L, len(s), len(t))
    out = [Fraction(0)] * L
    for i in range(L):
        if s[i]:
            for j in range(L - i):
                if t[j]:
                    out[i + j] += s[i] * t[j]
    return out


def expc(c, L):
    return [c ** n / factorial(n) for n in range(L)]


def D(s):
    return [s[n + 1] * (n + 1) for n in range(len(s) - 1)]


def theta(s, i):
    return [x * Fraction(n) ** i for n, x in enumerate(s)]


def zsh(s, j):
    return [Fraction(0)] * j + s[:len(s) - j]


stats = {}


def test(tag, desc, basis, ctrl=False):
    L = min(len(b) for b in basis)
    rows = [[b[n] for b in basis] for n in range(L)]
    rows = [r for r in rows if any(r)]
    K, E = len(basis), len(rows)
    if E - K < 5:
        return False
    res = analyze(rows)
    st = stats.setdefault(tag, [0, -99, '', 0])
    st[0] += 1
    st[3] = max(st[3], K)
    if res['excess'] > st[1]:
        st[1], st[2] = res['excess'], desc
    if res['kernel']:
        print(('CONTROL-HIT ' if ctrl else 'HIT ') + tag, desc, 'K', K, 'E', E, 'dim', len(res['kernel']))
        sys.stdout.flush()
    return True


def Vspace(c, dz, ke, L):
    out = []
    for k in range(ke + 1):
        e = expc(k * c, L)
        for j in range(dz + 1):
            out.append(zsh(e, j))
    return out


def bell_family(S, name, ctrl=False):
    L = len(S)
    S1 = D(S)
    S2 = D(S1)
    for c in CS:
        for ke in (1, 2):
            # B1
            for p in (0, 1, 2):
                for inh in (0, 1):
                    for dz in range(0, 20):
                        V = Vspace(c, dz, ke, L)
                        basis = [S1]
                        for i in range(p + 1):
                            Ti = theta(S, i)
                            basis += [mul(v, Ti, L) for v in V]
                        if inh:
                            basis += V
                        if not test(f'{name} B1 p={p} inh={inh} ke={ke}', f'c={c} dz={dz}', basis, ctrl):
                            break
            # B2
            for inh in (0, 1):
                for dz in range(0, 20):
                    V = Vspace(c, dz, ke, L)
                    basis = [S2] + [mul(v, S1, L) for v in V] + [mul(v, S, L) for v in V]
                    if inh:
                        basis += V
                    if not test(f'{name} B2 inh={inh} ke={ke}', f'c={c} dz={dz}', basis, ctrl):
                        break
            # B2' algebraic order-2 ODE, degree <= 2, coefficients in V(c,0,ke)
            if ctrl:
                continue
            fs = [S[:L - 2], S1[:L - 2], S2]
            mons = [[Fraction(1)] + [Fraction(0)] * (L - 3)]
            for D_ in (1, 2):
                for cmb in itertools.combinations_with_replacement(range(3), D_):
                    t = mons[0]
                    for v in cmb:
                        t = mul(t, fs[v], L - 2)
                    mons.append(t)
            V = Vspace(c, 0, ke, L - 2)
            basis = [mul(v, m, L - 2) for v in V for m in mons]
            test(f'{name} B2alg deg<=2 ke={ke}', f'c={c}', basis)


def subst(F, c, L):
    """coefficients of F(x/(1-cx)) = sum_n F_n x^n (1-cx)^{-n}"""
    out = [Fraction(0)] * L
    for n in range(L):
        if F[n]:
            for m in range(n, L):
                out[m] += F[n] * comb(m - 1, n - 1) * c ** (m - n) if n >= 1 else 0
    out[0] += F[0]
    return out


def subst_family(F, name, ctrl=False):
    L = len(F)
    for c in CS:
        G = subst(F, c, L)
        G2 = subst(F, 2 * c, L)
        for inh in (0, 1):
            for d in range(0, 30):
                basis = [zsh(F, j) for j in range(d + 1)] + [zsh(G, j) for j in range(d + 1)]
                if inh:
                    basis += [zsh([Fraction(1)] + [Fraction(0)] * (L - 1), j) for j in range(d + 1)]
                if not test(f'{name} B3 F(x/(1-cx)) inh={inh}', f'c={c} d={d}', basis, ctrl):
                    break
            for d in range(0, 30):
                basis = [zsh(F, j) for j in range(d + 1)] + [zsh(G, j) for j in range(d + 1)] + [zsh(G2, j) for j in range(d + 1)]
                if not test(f'{name} B3 F, F(x/(1-cx)), F(x/(1-2cx)) inh=0', f'c={c} d={d}', basis, ctrl):
                    break


L = NMAX + 1
a = [1] + [A[n] for n in range(1, L)]
EG = [Fraction(a[n], factorial(n)) for n in range(L)]
EGm = [x * (-1) ** n for n, x in enumerate(EG)]
bases = {
    'A': EG,
    'A_ev': [(x + y) / 2 for x, y in zip(EG, EGm)],
    'A_od': [(x - y) / 2 for x, y in zip(EG, EGm)],
    'B_ev': [Fraction(a[2 * m], factorial(m)) for m in range(L // 2 + 1) if 2 * m < L],
    'B_od': [Fraction(a[2 * m + 1], factorial(m)) for m in range(L // 2) if 2 * m + 1 < L],
}
for name, S in bases.items():
    bell_family(S, 'EGF ' + name)
OG = [Fraction(x) for x in a]
ogf = {
    'F': OG,
    'F_ev': [x if n % 2 == 0 else Fraction(0) for n, x in enumerate(OG)],
    'F_od': [x if n % 2 == 1 else Fraction(0) for n, x in enumerate(OG)],
    'Fe=sum a(2m)x^m': [OG[2 * m] for m in range(L) if 2 * m < L],
    'Fo=sum a(2m+1)x^m': [OG[2 * m + 1] for m in range(L) if 2 * m + 1 < L],
}
for name, F in ogf.items():
    subst_family(F, 'OGF ' + name)

print()
print(f"{'ansatz':52s} {'boxes':>5s} {'maxK':>5s}  best excess (box)")
for tag, st in stats.items():
    print(f"{tag:52s} {st[0]:5d} {st[3]:5d}  {st[1]:+d} ({st[2]})")

# controls
stats.clear()
bell = [Fraction(1)]
for n in range(L):
    bell.append(sum(comb(n, k) * bell[k] for k in range(n + 1)))
CS[:] = [Fraction(1)]
bell_family([bell[n] / factorial(n) for n in range(L)], 'CONTROL Bell', ctrl=True)
w = [Fraction(1)]
for n in range(L):
    w.append(sum(comb(n, k) * 2 ** (n - k) * (k + 1) * w[k] for k in range(n + 1)))
CS[:] = [Fraction(2)]
bell_family([w[n] / factorial(n) for n in range(L)], 'CONTROL weighted', ctrl=True)
# OGF substitution control: F = sum n! x^n?  use F(x) = 1/(1-x) * F(x/(1-x)) solution: Bell numbers OGF
CS[:] = [Fraction(1)]
# Bell OGF B(x) satisfies B(x) = 1 + x/(1-x) B(x/(1-x))
subst_family([Fraction(b) for b in bell[:L]], 'CONTROL Bell OGF', ctrl=True)
