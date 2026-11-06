# Recurrence classes and superexponential growth: literature notes (2026-11-06)

a(N) is the number of semi-symmetric fold sequences. The conjecture is
a(N) = N!/(κ ln N)^N. Then b_n = a(n)/n! ≈ e^{−n lnln n − n ln κ}, so the EGF would be an
entire function of infinite order.

Labels: [V] verified against a source, [K] standard literature, [I] inference.

## Which recurrence classes are compatible with this growth

| class | compatible? |
|---|---|
| C-finite | no (proven lower bound) |
| P-recursive / D-finite | **no, if the conjecture holds** (Birkhoff–Trjitzinsky asymptotic shape) [K/I] |
| D-algebraic EGF, order 1 | no: Gol'dberg / Malmquist–Yosida give finite order [K/I] |
| D-algebraic EGF, order ≥ 2 | **yes**: Maillet–Popken bounds allow it; Bell numbers (EGF e^{e^z−1}) are the model case [V] |
| D-algebraic OGF | not excluded by growth, but the Bell-number OGF is provably not D-algebraic (Klazar; Bostan–Di Vizio–Raschel), so look at the EGF [V] |
| binomial convolution / Bell-type (F' = G·F) | **yes**, the most natural class [I] |
| polynomial-recursive (Cadilhac et al.) | not excluded by growth; such a sequence is eventually periodic mod every large prime [V] |
| Somos / Laurent, q-holonomic | no (log a ~ n² or quasi-polynomial) [K/I] |
| catalytic-variable equations | no (algebraic, so exponential); substitution equations F(x) = R(x)F(x/(1−cx)) remain possible [I] |

## Examples with similar growth
- **Bell numbers**: n!/(ln n)^n·e^{O(n lnln n/ln n)}.
- **Anti-coprime permutations**: n!/(ln n)^{(e^{−γ}+o(1))n} (Pomerance).
- **Prime-sum / prime-circle permutations** (A051252): conjecturally of the same shape. These are permanents with no known recurrence.
- **3-AP-free (A003407)**: exponential, with no growth rate (Ho 2026, arXiv:2602.13617).

## Observations on our data
- The sequence is **not a moment sequence**: Hankel determinants have mixed signs, so there is no positive S- or J-fraction.
- **Parity:** the even and odd subsequences are each log-convex, but the full sequence is not. a(N)/(N·a(N−1)) alternates about 0.29 / 0.24, so fit each parity separately.
- **Prime factors:** large cofactors (e.g. a 23-digit cofactor at N = 37) rule out hypergeometric or product formulas.
- **EGF:** F'/F has factorially growing coefficients, so the EGF has zeros. The truncated EGF's zeros are stable to 6 digits: −0.397402 ± 1.43163i, −1.48491 ± 0.793053i, 0.68799 ± 1.82464i.
- **κ:** poorly determined. Fits give about 1.40 (even N) and 0.98 (odd N).

## Prioritised ansätze
1. Split every fit and guess by parity.
2. Bell-type EGF tests: order-2 algebraic differential equations, F' = G·F with G ∈ Q[z, e^{cz}], and OGF substitution equations.
3. Asymptotic model selection: −N ln(κ ln N) versus −cN lnln N versus a Bell saddle point.
4. Doubling/convolution relations with binomial weights.
5. a(N) mod p at larger N, to test eventual periodicity.
6. EGF zeros and values as PSLQ fingerprints.

The full report, with every citation, is reproduced in the session; the key URLs:
- https://arxiv.org/pdf/2002.08630
- https://arxiv.org/abs/2012.15292v4
- https://ar5iv.labs.arxiv.org/html/2206.01699
- https://arxiv.org/pdf/2203.06268
- https://arxiv.org/html/2602.13617v1
- https://github.com/T3gu1a/D-algebraic-functions
- https://arxiv.org/pdf/2202.07966
- https://ar5iv.labs.arxiv.org/html/1907.02645
