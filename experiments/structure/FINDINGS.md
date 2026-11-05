# Structure exploration: findings

The scripts are in this directory. `dp.c` is a generic subset DP for all the variants;
its modes are listed in the file header. Everything was run on 1 core with N ≤ 20,
except where noted. Notation: a(N) = number of semi-symmetric sequences;
g(S) = number of valid orderings that build S; r_m = min(m−1, N−m).

**Bottom line:** no closed form, recursion or OEIS match for a(N) or for any natural
refinement of it. The exact formulas found are all for degenerate relaxations.
An explicit product model comes close to a(N).

## Exact results
| object | result | checked |
|---|---|---|
| one panel m constrained (all others free) | N!·(2r)!!/(2r+1)!! = N!·4^r r!²/(2r+1)! (Wallis factor) | N ≤ 11 |
| radius capped at 1 | 2·E_N, the alternating permutations (A001250): each panel's time is a peak or a valley among its neighbours | N ≤ 9 |
| cyclic Z_N, half-circle windows (also the mod-2 version) | N!! = 2^{N/2}(N/2)! for even N, 0 for odd N ≥ 3: antipodal pairs must be placed consecutively | small N |
| cyclic symmetric (3-AP-free mod N) | 2^{N−1} at N = 2^k, 0 otherwise | N ≤ 18 (matches Goh–Zhao) |
| cyclic, radius 1 | N·E_{N−1} (A009752) | small N |
| left-half-only constraints, even N | left(2n) = 2n·left(2n−1) (panel 2n lies in no constrained window) | trivial |
| parity blocks | g(evens) = a(⌊N/2⌋) and g(odds) = a(⌈N/2⌉) | N ≤ 20 |

## Parity construction
- **One level:** evens then odds, or the reverse. This gives a(2n) ≥ 2a(n)² and
  a(2n+1) ≥ 2a(n)a(n+1).
  - Its share of a(N) falls from 0.80 at N=4 to 0.0016 at N=20.
  - So a(2n)/a(n)² is unbounded, unlike the 3-free bound of 21.
- **Recursive:** applying it at every level gives exactly 2^{N−1} sequences, so
  a(N) ≥ 2^{N−1}.
  - For N = 2^k this family is exactly the Goh–Zhao cyclic 3-AP-free orderings.
  - The cyclic object is therefore a vanishingly small subfamily, not a model for a(N).
- **Ends parity:** the share of sequences whose first and last panels have the same
  parity rises from 0 to 0.38 (N = 2..12) and stays below ½. This is the opposite of
  Sharma's tendency for the 3-free case.

## Product (Wallis) model and asymptotics
- **Wallis model:** a_W(N) = N!·Π_m (2r_m)!!/(2r_m+1)!! treats the constraints as
  independent.
  - a/a_W stays within 13% for N ≤ 11 and is about 10.4 at N = 27.
  - log(a/a_W) ≈ 0.09·N, a mild positive correlation between constraints.
- **Random-prefix model:** assuming the earlier set is uniformly random gives a ratio
  between 0.84 and 1.006 for N ≤ 11, and 5.1 at N = 27.
- **Growth:** both models give log a ≈ ½·N log N + O(N).
  - Free fits give an N log N coefficient of 0.61 (odd N) to 0.75 (even N).
  - The data do not pin it down.
- **Per-step acceptance rate:** averaged over the middle steps, it is about
  1.14/log N for N ≤ 20. The heuristic says c/√N; q·√N is still creeping up
  (1.33 to 1.71).

## Arithmetic signal (weak)
After removing a smooth fit of log(a/a_W) within each parity class, the residual is
positive for N = 6, 9, 12, 15, 18, 21, 24, 27, and negative for nearly all other N
(N = 20 is the one exception). The effect is only 0.01–0.09 in log.
- A possible mechanism: creases N/3 and 2N/3 form the period-2 orbit of the doubling
  map, and are integers exactly when 3 | N. Not tested.
- Nothing distinguishes N = 2^k, N = 2^k ± 1, or the order of 2 mod N.
- **Prediction to test:** a(30) and a(33) should sit above trend.

## Refined statistics
None of these are in OEIS.
- **Valid prefixes of length k, T(N,k):**
  - T(N,1) = N.
  - T(N,2) = ⌊N²/2⌋.
  - T(N,N−1) = a(N).
  - The first-element column, T(N,3) and T(N,N−2) have no OEIS match.
- **Reachable sets:**
  - Size 2: ⌊N²/3⌋.
  - In total: about 0.82·2^N reachable; about 0.67·2^N live (also completable).
- **Fixed by reversal∘mirror:**
  - Counts: 1, 2, 0, 6, 4, 12, 0, 76, 16, 274, 0, 1088, 708, 5696, 0.
  - The count is 0 for N ≡ 3 (mod 4).
  - a(N) ≡ (this count) (mod 4) (see `experiments/arith/FINDINGS.txt`; earlier "2×" was wrong).
- **Middle panel (odd N):**
  - It can only be placed at odd steps.
  - N = 7 is uniform: 64 at each of the 4 odd steps.
  - a(7) = 2^8 is a coincidence: N = 9 gives 696, 1188, 488, 1188, 696, and every
    a(N) with N ≥ 8 has an odd factor.

## Negative results
- **No smaller state than S:** no statistic coarser than the set S predicts f(S).
  The best key tried (|S| plus the sequence of window imbalances) compresses no further
  than mirror symmetry.
- **Valid prefixes are only somewhat smoother than random sets:** discrepancy 1.42 vs
  1.72 at N = 20, and it still grows with N.
- **No structured family dominates the sum:** in Σ g(S)g(S^c) over half-size sets, the
  two parity classes are the heaviest single sets, but the weight is spread over about
  0.24·C(N, N/2) sets.
- **No OEIS match** for left-half-only, mod-2, one-sided (left ≥ right), or radius caps
  of 2 or 3.

## Most promising leads
1. **Correlation (cluster) expansion of log(a/a_W).** The pairwise joint probabilities
   P(C_m ∧ C_m′) are exactly computable. This could explain the e^{0.09N} drift and
   settle the true asymptotics.
2. **Confirm the mod-3 effect** with a(28..33) from the Rust counter.

## Update: mod-3 effect confirmed with a(28..33) (Rust counter)
Let y(N) = log(a(N)/a_W(N)). Compare each N with its same-parity neighbours using the
local bump b(N) = y(N) − (y(N−2)+y(N+2))/2. No trend fit is needed.

| N | 6* | 7 | 8 | 9* | 10 | 11 | 12* | 13 | 14 | 15* | 16 | 17 | 18* | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| b | +.060 | −.165 | −.037 | +.104 | −.052 | −.070 | +.026 | −.054 | −.046 | +.040 | −.035 | −.034 | +.014 | −.050 | −.022 |

| N | 21* | 22 | 23 | 24* | 25 | 26 | 27* | 28 | 29 | 30* | 31 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| b | +.025 | −.040 | −.032 | +.016 | −.027 | −.029 | +.007 | −.024 | −.018 | +.006 | −.033 |

- b(N) > 0 for **every** N ≡ 0 (mod 3) in 6..30.
- b(N) < 0 for **every** other N in 7..31.
- The bump decays roughly like 1/N.
- Extrapolating a quadratic trend fitted on N ≤ 27 is unreliable (the trend bends),
  hence this local test.
