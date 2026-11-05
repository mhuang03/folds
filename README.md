# Folds: symmetric and semi-symmetric bisection orders

Panels `1..N`. A fold sequence is a permutation `a` of `[1..N]`, and step `k` bisects
panel `m = a_k`. Let `S` be the set of panels bisected before step `k`. The window around
`m` reaches `r = min(m-1, N-m)` panels on each side.

* **symmetric step:** for all `1 ≤ d ≤ r`, `m-d ∈ S ⇔ m+d ∈ S`
* **semi-symmetric step:** `#{d ≤ r : m-d ∈ S} = #{d ≤ r : m+d ∈ S}`

Two corrections to the informal statement: the window size depends on the *panel*
`a_k`, so it is `min(a_k - 1, N - a_k)`, not `min(k-1, N-k)`. And the semi-symmetric
count tests `a_k ± d ∈ S`, not `a_{k±d}`.

## Lean (`Folds/`, Lean 4 core only, no Mathlib). Build with `lake build`

| file | contents |
|---|---|
| `Defs.lean` | `reach`, `IsFoldSeq`, `SymStep`, `SemiStep`, `Symmetric`, `SemiSymmetric`, `APFree` |
| `Basic.lean` | `Symmetric.semiSymmetric`, `symmetric_iff_apFree`, `semiStep_iff_of_compl`, `SemiSymmetric.reverse`, `SemiSymmetric.mirror` |
| `Decide.lean` | Bool checkers proven equal to the Props (decidability) |
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
