# Folds: symmetric and semi-symmetric bisection orders

Panels `1..N`. A fold sequence is a permutation `a` of `[1..N]`, and step `k` bisects
panel `m = a_k`. Let `S` be the set of panels bisected before step `k`. The window around
`m` reaches `r = min(m-1, N-m)` panels on each side.

* **symmetric step:** for all `1 ≤ d ≤ r`, `m-d ∈ S ⇔ m+d ∈ S`
* **semi-symmetric step:** `#{d ≤ r : m-d ∈ S} = #{d ≤ r : m+d ∈ S}`

Two corrections to the informal statement: the window size depends on the *panel*
`a_k`, so it is `min(a_k - 1, N - a_k)`, not `min(k-1, N-k)`. And the semi-symmetric
count tests `a_k ± d ∈ S`, not `a_{k±d}`.

## Lean (`Folds/`). Build with `lake exe cache get && lake build`. Files marked (Mathlib) use Mathlib

| file | contents |
|---|---|
| `Defs.lean` | `reach`, `IsFoldSeq`, `SymStep`, `SemiStep`, `Symmetric`, `SemiSymmetric`, `APFree` |
| `Basic.lean` | `Symmetric.semiSymmetric`, `symmetric_iff_apFree`, `semiStep_iff_of_compl`, `SemiSymmetric.reverse`, `SemiSymmetric.mirror` |
| `Decide.lean` | Bool checkers proven equal to the Props (decidability) |
| `Parity.lean` | `middle_index_even`: for odd N, the middle panel is always placed at an odd step |
| `Blocks.lean` | `semiSymmetric_blocks_iff`: evens-then-odds (or the reverse) is semi-symmetric iff both halves are; `prefix_class_semiSymmetric` |
| `Counting.lean` (Mathlib) | `semiCount_even`: a(2n) ≥ 2a(n)²; `semiCount_odd`: a(2n+1) ≥ 2a(n)a(n+1); `semiCount_ge_pow`: a(N) ≥ 2^{N−1}; `card_class_prefix` (exact count of sequences that start with a full parity class) |
| `RevMirror.lean` | reversal∘mirror preserves semi-symmetry; `revMirror_no_fixed`: no fixed points when N ≡ 3 (mod 4) |
| `Radius.lean` | capped-radius variant; radius 1 ⇔ each panel's time is a local max or min relative to its neighbours |
| `Recursion.lean` (Mathlib) | **the recursion**: `g_eq_sum`, `semiCount_eq_g`, and the reversal/meet-in-the-middle identity `semiCount_eq_sum_split`: a(N) = Σ_{|S|=k} g(S)·g(Sᶜ) |
| `Congruence.lean` (Mathlib) | `semiCount_mod_four`: a(N) ≡ c(N) (mod 4), where c(N) is the number of sequences fixed by reversal∘mirror; a(N) even for N ≥ 2; `semiCount_mod_four_of_three`: 4 ∣ a(N) when N ≡ 3 (mod 4) |
| `Prefix.lean` (Mathlib) | `card_prefixTwo`: there are ⌊N²/2⌋ valid 2-step prefixes; `card_reachTwo`: ⌊N²/3⌋ reachable 2-sets |
| `Wallis.lean` (Mathlib) | `card_wallisSeqs`: exactly N!·4^r·r!²/(2r+1)! permutations satisfy a single panel's constraint |
| `SelfDual.lean` (Mathlib) | `card_revMirrorFixed`: c(N) = number of valid half sequences; flip lemmas and a mod-4 reduction of c(N) for even N |
| `Cyclic.lean` | `semiStep_iff_cyclicStep` (cyclic/doubling form, all `N`), prefix forms `semiStep_iff_left`/`_right`, interval-count forms, complement lemmas, `deadEnd_four` |

The theorems in `Basic.lean` are proven for all `N`. Brute-force counting is done
outside Lean (see `experiments/` and the Rust crate), not with `native_decide`.

## Data (`experiments/semi_counts.txt`, computed by `experiments/semi.c`)

Semi-symmetric counts for `N = 1..27`:
1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
2505681033958, 18168130281086, 119006527671252, 979730153850974,
6564449510287388, 55581983250573500, 413109755332919448.

The symmetric counts are OEIS A003407 (permutations with no 3-term AP), as expected.
The semi-symmetric sequence is **not in the OEIS**.

## Equivalent formulations

1. **Symmetric ⇔ 3-AP-free** (proven: `symmetric_iff_apFree`).
2. **Prefix counts.** Let `P(j) = |S ∩ [1,j]|` and `s = |S|`. For `m ∉ S`:
   * left half (`2m-1 ≤ N`): the step is OK iff `P(2m-1) = 2·P(m-1)`. The crease
     `2m-1` is the reference fold.
   * right half: the step is OK iff `s + P(2m-1-N) = 2·P(m-1)`.
3. **Cyclic / doubling form.** Wrap the strip into a circle of length `N` and extend
   `P` by `P̃(j) = P(j mod N) + ⌊j/N⌋·s`. Both cases then read **`P̃(2m-1) = 2·P(m-1)`**.
   With the panel centre `c = m - ½`, the counting function `F` and the discrepancy
   `E(x) = F(x) - s·x/N` (period `N`), this becomes **`E(2c) = 2·E(c)`**: placing the
   panel at `c` is allowed iff the discrepancy doubles under the doubling map
   `x ↦ 2x (mod N)`. (Proven in Lean: `semiStep_iff_cyclicStep`.)
4. **Complement / reversal.** A step's validity is unchanged if `S` is replaced by its
   complement inside the window. Hence reversing a semi-symmetric sequence gives a
   semi-symmetric one (proven), and so does mirroring `m ↦ N+1-m` (proven). For
   `N ≤ 8` these are the only value-relabelings that preserve the set.

## Recursion

The condition depends only on the *set* `S`, not on the order it was built in. So with
`g(∅) = 1`:

    g(S ∪ {m}) += g(S)   whenever m ∉ S and the step (S, m) is semi-symmetric,
    a(N) = g([1..N]).

Reversal gives a meet-in-the-middle identity, checked for `N ≤ 12`:

    a(N) = Σ_{|S| = k} g(S) · g([1..N] \ S)    for every k,

so only sets of size `≤ ⌈N/2⌉` are needed.

## Why I don't expect a closed form

* The terms have huge prime factors (e.g. `a(24) = 2 · 489865076925487`), which rules
  out product formulas.
* There is no linear recurrence with polynomial coefficients of order ≤ 5 and degree ≤ 5
  (`experiments/guess.py`).
* The growth is between exponential and factorial: `log a(N) / log N! ≈ 0.63` for
  `N = 15..27`. Even `N` is relatively larger than odd `N`, because for odd `N` the middle
  panel requires the two halves to be exactly balanced.
* The symmetric analogue, A003407, has no known closed form either.

## Practical note: dead ends

A partial semi-symmetric sequence cannot always be completed. The smallest example is
`N = 4`: bisect panels 1 then 4, and no next step is valid. Dead-end states for
`N = 4..14`: 1, 2, 4, 18, 30, 63, 137, 293, 591, 1275, 2449.

## Further findings

- `experiments/structure/FINDINGS.md`. Exact formulas for relaxations: a single
  constraint gives a Wallis factor, and radius 1 gives 2·E_N (alternating
  permutations). Parity blocks give a(N) ≥ 2^{N−1} and a(2n) ≥ 2a(n)². The independent
  product model a_W(N) = N!·Π(2r)!!/(2r+1)!! is within a factor of about 10 at N = 27.
  There is a weak mod-3 signal.
- `docs/LITERATURE.md`. Survey of 3-AP-free permutations (A003407) and their cyclic
  versions, and the OEIS searches (no matches).
- `experiments/arith/FINDINGS.txt`. Burnside analysis under reversal and mirror. c(N), the
  number of sequences unchanged by reversal∘mirror, is computed to N = 41 using a
  half-size 3^{N/2}-state reformulation. a(N) ≡ c(N) (mod 4), and 4 | a(N) when
  N ≡ 3 (mod 4). The mod-3 growth effect is statistically significant. Empirical
  log-size laws: minimum descents ⌊log2(N+1)⌋−1, and maximum number of free steps.
- `experiments/cluster/FINDINGS.txt`.
  - Exact pair correlations of the panel constraints, including the rule for when they
    vanish and a large-window limit law K(γ).
  - Exact Stirling asymptotics for the Wallis model.
  - The asymptotic fit log a ≈ c·N log N − 0.82N + …, with c ≈ 0.66 and still rising.
  - The mechanism of the mod-3 effect: the period-2 doubling orbit {N/3, 2N/3}, whose
    two constraints read the same two prefix sets and force P(N/3) ≈ s/3.
