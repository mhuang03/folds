# Folds: symmetric and semi-symmetric bisection orders

Panels `1..N` lie between existing creases. A **fold sequence** is a permutation `a` of
`[1..N]`, and step `k` bisects panel `m = a_k` by folding the nearer edge onto a
reference crease. Let `S` be the set of panels bisected before step `k`. The panels
between the edge and the crease are `m ± d` for `1 ≤ d ≤ r`, with `r = min(m-1, N-m)`.

* **symmetric step:** for all `d ≤ r`, `m-d ∈ S ⇔ m+d ∈ S`
* **semi-symmetric step:** `#{d ≤ r : m-d ∈ S} = #{d ≤ r : m+d ∈ S}`

`a(N)` is the number of sequences in which every step is semi-symmetric.

Two corrections to the informal statement: the window size depends on the *panel*
`a_k`, so it is `min(a_k - 1, N - a_k)`, not `min(k-1, N-k)`. And the count tests
`a_k ± d ∈ S`, not `a_{k±d}`.

## Status at a glance

| question | status |
|---|---|
| closed form for a(N) | **none found; very unlikely**. No OEIS match; huge prime factors; no holonomic recurrence; even the symmetric analogue A003407 has no known formula (and, per Ho 2026, no exponential growth rate) |
| recursive formula | **proven** (Lean): subset recursion `g`, and a(N) = Σ_{\|S\|=k} g(S)·g(Sᶜ) for every k |
| terms | a(1..35) exact; ln a(N) estimated to N = 4096 |
| exact formulas for pieces | T(N,2) = ⌊N²/2⌋ and the period-6 quasi-polynomial T(N,3) (both **proven**); T(N,4) has period 168 (fitted); single-panel Wallis count (**proven**) |
| congruences | a(N) ≡ c(N) (mod 4) (**proven**); 4 ∣ a(N) for N ≡ 3 (mod 4) (**proven**); no patterns modulo odd primes |
| growth | rigorously ½e^{1.28N} ≤ a(N) ≤ N!·e^{−Θ(N)}. **Conjecture:** a(N) = N!/(κ ln N)^N |
| arithmetic effect | multiples of 3 sit above trend (all N ≤ 33). Mechanism: the 2-cycle {N/3, 2N/3} of the doubling map |

Here T(N,k) is the number of valid k-step prefixes, and c(N) is the number of sequences
fixed by reversal∘mirror.

## Data

`experiments/semi_counts.txt`: N ≤ 27 come from `experiments/semi.c`; N = 28..35 come
from the Rust crate `rust/`.

a(1..35) = 1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328,
9167908, 47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
2505681033958, 18168130281086, 119006527671252, 979730153850974,
6564449510287388, 55581983250573500, 413109755332919448, 3603074636066234798,
27545080998591561856, 262878496654501774250, 2037247307316034896720,
20222490725552617395966, 171668579369815966705184, 1711977358970374039688092,
14916356465581456801127844.

- The symmetric counts are OEIS A003407 (3-AP-free permutations).
- c(N), for sequences fixed by reversal∘mirror, is known to N = 41
  (`experiments/arith/`).
- `rust/` uses a mirror-orbit, meet-in-the-middle layered DP: a(33) takes 74 s. N ≥ 36
  needs more than 15 GB of RAM (see `rust/README.md`).

## Equivalent formulations (all proven in Lean)

1. **Symmetric ⇔ 3-AP-free.** No x, y with (x+y)/2 bisected between them.
2. **Prefix form.** With `P(j) = |S ∩ [1,j]|` and `s = |S|`:
   - left half: `P(2m−1) = 2P(m−1)`;
   - right half: `s + P(2m−1−N) = 2P(m−1)`.
3. **Cyclic / doubling form.** `P̃(2m−1) = 2P(m−1)` with `P̃(j) = P(j mod N) + ⌊j/N⌋s`.
   Equivalently, the discrepancy `E(x) = F(x) − s·x/N` on `R/NZ` must satisfy
   `E(2c) = 2E(c)` at the panel centre `c = m−½`. This is a doubling-map condition.
4. **Window rule.** Let `A` and `B` be the numbers of earlier panels above and below
   `m`.
   - `A < B`: `m` is in the right half, and its window holds the A panels above it plus
     exactly the A nearest below.
   - `A > B`: the mirror case.
   - `A = B`: the window covers all of `S`.
5. **Complement.** Swapping placed and unplaced panels inside the window preserves
   validity. Hence reversal and mirror invariance.
6. **Binary digits** (N = 2^L). The step condition splits into one doubling-balance term
   per 1-bit of `m−1`.

## Lean formalization (`Folds/`)

Build with `lake exe cache get && lake build`. There is no `sorry` and no
`native_decide`. Files marked (M) use Mathlib.

| file | main results |
|---|---|
| `Defs` | definitions: `reach`, `IsFoldSeq`, `SymStep`, `SemiStep`, `Symmetric`, `SemiSymmetric`, `APFree` |
| `Basic` | symmetric ⇒ semi-symmetric; `symmetric_iff_apFree`; complement lemma; reversal and mirror invariance |
| `Decide` | decidability via Bool checkers |
| `Cyclic` | `semiStep_iff_cyclicStep` (doubling form); prefix forms; interval-count forms |
| `Parity` | `middle_index_even`: for odd N, the middle panel is always placed at an odd step |
| `Blocks` | `semiSymmetric_blocks_iff`: evens-then-odds is valid iff both halves are |
| `RevMirror` | reversal∘mirror is an involution; no fixed points when N ≡ 3 (mod 4) |
| `Radius` | radius-1 relaxation ⇔ every panel's time is a local max or min relative to its neighbours |
| `Counting` (M) | a(2n) ≥ 2a(n)², a(2n+1) ≥ 2a(n)a(n+1), a(N) ≥ 2^{N−1}; exact count of sequences that start with a full parity class |
| `Recursion` (M) | **recursion** `g_eq_sum`, `semiCount_eq_g`; split identity `semiCount_eq_sum_split` |
| `Congruence` (M) | `semiCount_mod_four`: a ≡ c (mod 4); a(N) even; 4 ∣ a(N) when N ≡ 3 (mod 4) |
| `Prefix` (M) | ⌊N²/2⌋ valid 2-prefixes; ⌊N²/3⌋ reachable 2-sets |
| `WindowRule` (M) | window rule (iff); valid suffixes = valid prefixes; **T(N,3) closed form**: 36·T(N,3) = 8N³ − 3N² − (30 if N even, else 12)N + (0,7,8,−9,16,−1)[N mod 6] |
| `Wallis` (M) | a single panel's constraint holds for exactly N!·4^r·r!²/(2r+1)! permutations |
| `SelfDual` (M) | c(N) = number of valid half sequences; flip lemmas |
| `Extremal` (M) | maximum left-to-right maxima = ⌊log₂N⌋+1; maximum free steps = ⌊log₂(N+1)⌋+⌊log₂((N+1)/3)⌋+1; shifted parity blocks |
| `Growth` (M) | **composition** a(qn) ≥ a(q)·a(n)^q; doubling splits a(3n) ≥ 2a(n)a(2n) (also 5n, 7n); branching and parity upper bounds |
| `Asymptotics` (M) | dipole lemma (how one panel changes the imbalance field); binary-digit decomposition; half-circle balance |
| `Descents` (M) | N+1 ≤ (⌊log₂(N+1)⌋+2)^(des+1); the same for LDS and LIS |
| `Independence` (M) | exact independence of constraints: compatible windows (disjoint, or one window inside an arm of the other) give #(C_a ∧ C_b) = N!·w_a·w_b; chain product formula `card_constrSeqs_chain`; dyadic upper bound `semiCount_mul_le_dyadic` |
| `Live` (M) | every first panel extends to a full sequence; every dead 2- and 3-prefix is proven dead |

## Conjectures and open problems

1. **Asymptotics.** a(N) = N!/(κ_N ln N)^N, i.e. ln a = N ln N − N ln ln N − O(N).
   Evidence: debiased SMC to N = 4096 and a Feynman–Kac model; see
   `experiments/asymptotics/NOTES.txt`. Rigorously, nothing super-exponential is known
   in either direction.
2. **Mod-3 effect.** Relative to the independence model, a(N) is above trend exactly
   when 3 ∣ N (all N ≤ 33). The proposed mechanism is the 2-cycle {N/3, 2N/3} of the
   doubling map.
3. **T(N,k)** is a quasi-polynomial for every fixed k: proven via an Ehrhart
   (polytope-counting) decomposition. The leading coefficients are exact for k ≤ 7. The
   period of T(N,5) is unknown (likely 1680).
4. **Minimum LDS = minimum LIS = ⌊log₂(N+1)⌋**, attained. Minimum descents are
   ⌊log₂(N+1)⌋−1, except ⌊log₂(N+1)⌋ at N = 25, 55, 57, 59. This would follow from the
   labelling conjecture (equivalently: every *right-heavy* permutation of [N] has a
   decreasing subsequence of length ⌊log₂(N+1)⌋). The SAT check has reached t = 5
   (N = 63..66). There is no proof yet: the extremal labellings are not unique for t ≥ 4;
   see `experiments/labelling/PROOFS.txt`.
5. **Liveness.** Every valid 2-prefix is live except (1,N) and (N,1) for even N and
   (1,7), (7,1) at N = 7. Checked for N ≤ 31.

## Where things are

| directory | contents |
|---|---|
| `rust/` | the fast exact counter (see its README) |
| `experiments/structure/FINDINGS.md` | relaxations, Wallis model, parity blocks, refined statistics |
| `experiments/arith/FINDINGS.txt` | Burnside / mod 4, c(N) to 41, statistics polynomials |
| `experiments/cluster/FINDINGS.txt` | pair correlations, mod-3 mechanism, Wallis asymptotics |
| `experiments/prefix/FINDINGS.txt` | T(N,k) quasi-polynomials, Ehrhart mechanism, window rule |
| `experiments/extremal/PROOFS.txt` | left-to-right maxima and free-step laws |
| `experiments/growth/PROOFS.txt` | composition, splits, upper bounds, SMC |
| `experiments/asymptotics/NOTES.txt` | the N!/(κ ln N)^N conjecture, SMC to 4096 |
| `experiments/descents/PROOFS.txt` | descent and LDS bounds, SAT data |
| `experiments/independence/PROOFS.txt` | pair independence, including the one-outside-element case (paper) |
| `experiments/labelling/PROOFS.txt` | labelling / right-heavy reformulation of the descent bound, failed and surviving lemma candidates |
| `experiments/live/FINDINGS.txt` | dead and live prefixes, Beatty copies |
| `docs/LITERATURE.md` | literature and OEIS survey |

## Practical note for folders

A partial semi-symmetric sequence can get stuck. For example, with N = 4, bisecting
panels 1 then 4 leaves no valid move. Two families that never get stuck:
- the "parity block" order: bisect all even panels (recursively, in a valid order for
  ⌊N/2⌋ panels), then all odd ones, or the reverse;
- when q ∣ N, the same by residue classes mod q: whole classes in the order of a valid
  q-sequence, each class internally in a valid (N/q)-order (the composition theorem).
