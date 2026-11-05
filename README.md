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
| closed form for a(N) | **none found; very unlikely**. The prefix-count bivariate generating function is provably not D-finite. No OEIS match; huge prime factors; no holonomic recurrence; even the symmetric analogue A003407 has no known formula (and, per Ho 2026, no exponential growth rate) |
| recursive formula | **proven** (Lean): subset recursion `g`, and a(N) = Σ_{\|S\|=k} g(S)·g(Sᶜ) for every k |
| terms | a(1..37) exact; ln a(N) estimated to N = 4096 |
| exact formulas for pieces | T(N,2) = ⌊N²/2⌋ and the period-6 quasi-polynomial T(N,3) (**proven in Lean**). **Exact** quasi-polynomials for T(N,4), T(N,5) and T(N,6), with periods 168, 1680 and 104160, derived from Ehrhart generating functions. The period of T(N,7) is 624960. Single-panel Wallis count (**proven**) |
| congruences | a(N) ≡ c(N) (mod 4) (**proven**); 4 ∣ a(N) for N ≡ 3 (mod 4) (**proven**); no patterns modulo odd primes |
| growth | **rigorously (N/512)^{N/22} ≤ a(N) ≤ N!·e^{−Θ(N)}** (super-exponential lower bound, proven in Lean; a(N) ≥ (N/2)^{N/6} for N = 2^L). **Conjecture:** a(N) = N!/(κ ln N)^N |
| arithmetic effect | multiples of 3 sit above trend (all N ≤ 33). Mechanism: the 2-cycle {N/3, 2N/3} of the doubling map |

Here T(N,k) is the number of valid k-step prefixes, and c(N) is the number of sequences
fixed by reversal∘mirror.

## Data

`experiments/semi_counts.txt`: N ≤ 27 come from `experiments/semi.c`; N = 28..37 come
from the Rust crate `rust/`.

a(1..37) = 1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328,
9167908, 47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
2505681033958, 18168130281086, 119006527671252, 979730153850974,
6564449510287388, 55581983250573500, 413109755332919448, 3603074636066234798,
27545080998591561856, 262878496654501774250, 2037247307316034896720,
20222490725552617395966, 171668579369815966705184, 1711977358970374039688092,
14916356465581456801127844, 162918548122441960881265188, 1435459602925600924848243286.

- The symmetric counts are OEIS A003407 (3-AP-free permutations).
- c(N), for sequences fixed by reversal∘mirror, is known to N = 41
  (`experiments/arith/`).
- `rust/` uses a mirror-orbit, meet-in-the-middle layered DP: a(33) takes 74 s. a(36) and a(37) used block streaming (6.2 and 11.2 GB
  peak) and 13 u8 CRT residues each (2.6 h and 4.6 h). N = 38 needs about 24 GB (see `rust/README.md`).

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
| `Copies` (M) | general doubling splits a((2j+1)n) ≥ 2a(jn)a((j+1)n) for all j; copy criterion (X is a copy ⇔ every element is a valid last step); Beatty copies; near-class copy for odd N |
| `ShiftedCount` (M) | a(2n) ≥ 2a(n)² + a(n−1)a(n+1) (odd n), and the halved version for even n |
| `Independence2` (M) | the one-outside-element independence case (`card_pair_one_outside` and its mirror), and chains ending in such a pair |
| `SuperExp` (M) | **super-exponential lower bound**: slip lemma; a(4m) ≥ 2^m·a(m)⁴; `self_pow_le_semiCount`: N^N ≤ 2^{3N}·a(N)^{32}; `pow_le_semiCount_pow_four`: (4^j)^{4^j} ≤ a(4^j)^8 |
| `SuperExp2` (M) | slip chains B(2m) ≥ 2^m a(m)² B(m); `pow_le_semiCount_pow_six`: N^N ≤ 2^N·a(N)^6 for N = 2^L; `self_pow_le_semiCount_pow_22`: N^N ≤ 2^{9N}·a(N)^{22} for all N ≥ 1 |
| `SuperExp3` (M) | general slip lemma (`blocks_mem_semiSeqs_iff`): "X in order f_τ, then Xᶜ in order g_σ" is valid iff τ, σ satisfy induced cyclic-interval conditions, for any split X; parity blocks, residue compositions and slips are special cases |
| `Live2` (M) | co-reachability; every residue class mod q is a window copy (any N); **residue chain theorem** (`res_chain`); a recursively defined proven family of live 2-sets (e.g. 523 of 779 at N = 40) |
| `Live3` (M) | Theorem E (`no_chain_exc`): no residue chain starts with class 1 at N ≡ 1 (mod q) when q is not a power of 2; Theorem H (`palindromic_chain`): explicit chains for every odd q, giving residue transfers for all odd q; near-class copies `winEmb_near` |
| `Live4` (M) | good classes ⇔ complete residue chains; block-chain composition `good_comp` (every class good for q = 2^a); palindromic chains; 378 kernel-checked certificates for q ≤ 27; family `Cov2` proving 3373 of 4949 non-dead 2-sets co-reachable at N = 100 |
| `Labelling` (M) | finite reduction for each label count t (`bound_of_checks`, via left-half monotonicity); t ≤ 2 settled for all N, so des + 1 ≥ min(⌊log₂(N+1)⌋, 3) |
| `Adjacent` (M) | **Theorem G** (inward-sign criterion ⇒ co-reachable, via a greedy-then-reverse construction); **every interval is co-reachable** (`coReach_interval`), hence the **Adjacent Lemma**; multiples of q are co-reachable when q ∣ N+1; family `Cov3` (4409 of 4949 non-dead 2-sets at N = 100) |
| `Generate` | **truncation theorem** (`truncation`, `gen_filter`): the truncated bit-reversal order, and every member of the recursive odds/evens-first tree family, is symmetric and semi-symmetric for every N; O(log N) direct access `genAt_eq`; Montgomery-ladder construction `ladder_valid` |
| `Live` (M) | every first panel extends to a full sequence; every dead 2- and 3-prefix is proven dead |

## Conjectures and open problems

1. **Asymptotics.** a(N) = N!/(κ_N ln N)^N, i.e. ln a = N ln N − N ln ln N − O(N).
   Evidence: debiased SMC to N = 4096 and a Feynman–Kac model; see
   `experiments/asymptotics/NOTES.txt`. Rigorously 1/22 ≤ liminf ln a/(N ln N), and
   limsup ≥ 1/6 (slip chains, `Folds/SuperExp2.lean`). Slip methods are capped at 1/2. The upper side is only
   N!·e^{−Θ(N)}.
2. **Mod-3 effect.** Relative to the independence model, a(N) is above trend exactly
   when 3 ∣ N (all N ≤ 33). The proposed mechanism is the 2-cycle {N/3, 2N/3} of the
   doubling map.
3. **T(N,k)** is a quasi-polynomial for every fixed k (proven via an Ehrhart
   decomposition, one polytope per order type).
   - Exact formulas exist for k ≤ 6; see `experiments/prefix5/FINDINGS.txt`.
   - **Period law** (upper bound **proven on paper for all k**, via McMullen /
     Berline–Vergne and a face lemma; exactness certified for k ≤ 7): the coefficient of N^(k−m) has period
     B(m) = lcm(2^(m−1), 2^a(2^s−1) : a+s = m−1), i.e. 1, 1, 2, 12, 168, 1680, 104160,
     624960.
   - The denominators are the periodic points of the doubling map: halving chains give
     2^a, and halving cycles give 2^s − 1.
   - **Theorem C (proven on paper):** for every k ≥ 4, 2^(k−1)·(2^(k−1)−1) divides the
     period of T(N,k). Cancellations (T(N,3); the 16-part at k = 5) come from one
     parity effect: the halving chain and the increasing chain are conjugate and cancel
     for odd k. Two-cycle faces give components of order 93 and 105 at k = 9.
   - **The bivariate generating function Σ T(N,k)tᴺuᵏ is not D-finite (proven)**, so
     there is no finite transfer structure in k. See `experiments/periods2/PROOFS.txt`.
   - Leading coefficients c_k are exact for k ≤ 9, e.g. 9!·c_9 ≈ 101.7. The continuum
     acceptance p_k = c_k/c_{k−1} decays like ≈ 0.75/(ln k + 0.25) (continuum SMC to
     k ≈ 1000), matching the a(N) = N!/(κ ln N)^N conjecture.
     See `experiments/periods/PROOFS.txt`.
4. **Minimum LDS = minimum LIS = ⌊log₂(N+1)⌋**, attained. Minimum descents are
   ⌊log₂(N+1)⌋−1, except ⌊log₂(N+1)⌋ at N = 25, 55, 57, 59. This would follow from the
   labelling conjecture (equivalently: every *right-heavy* permutation of [N] has a
   decreasing subsequence of length ⌊log₂(N+1)⌋). For each t this is a *finite* check (left-half
   monotonicity). It is now settled for every N when t ≤ 5 (t ≤ 2 in Lean; t = 3, 4, 5 by
   exhaustive search and SAT), so LDS ≥ min(⌊log₂(N+1)⌋, 6) and the descent bound holds for
   all N ≤ 126. See `experiments/labelling2/PROOFS.txt`. There is no proof yet: the extremal labellings are not unique for t ≥ 4;
   see `experiments/labelling/PROOFS.txt`.
5. **Liveness (Conjecture C).** Every 2-set is co-reachable (its complement can be
   ordered validly) except {1,N} for even N and {1,7} at N = 7. Checked for N ≤ 28 (and
   valid prefixes for N ≤ 31). The Adjacent Lemma, and co-reachability of every
   interval, are now **proven** (Lean, Theorem G). Still open: {1,N} for odd N, and
   some wide pairs (v − u odd and large) from N = 31 on. See
   `experiments/live2/PROOFS.txt`.

## Where things are

| directory | contents |
|---|---|
| `rust/` | the fast exact counter (see its README) |
| `experiments/structure/FINDINGS.md` | relaxations, Wallis model, parity blocks, refined statistics |
| `experiments/arith/FINDINGS.txt` | Burnside / mod 4, c(N) to 41, statistics polynomials |
| `experiments/cluster/FINDINGS.txt` | pair correlations, mod-3 mechanism, Wallis asymptotics |
| `experiments/prefix/FINDINGS.txt` | T(N,k) quasi-polynomials, Ehrhart mechanism, window rule |
| `experiments/prefix5/FINDINGS.txt` | exact T(N,5), T(N,6) via Normaliz; period law for the coefficients |
| `experiments/periods/PROOFS.txt` | proof of the period-law upper bound; c_8, c_9; continuum acceptance |
| `experiments/periods2/PROOFS.txt` | Theorem C (period divisibility), vertex classification, non-D-finiteness of the bivariate GF |
| `experiments/extremal/PROOFS.txt` | left-to-right maxima and free-step laws |
| `experiments/superexp/PROOFS.txt` | slip construction and the super-exponential lower bound |
| `experiments/superexp2/PROOFS.txt` | slip chains: exponents 1/6 (powers of 2) and 1/22 (all N), and the ceiling analysis |
| `experiments/superexp3/PROOFS.txt` | general slip lemma, and why interleavings resist certification (the regress) |
| `experiments/growth/PROOFS.txt` | composition, splits, upper bounds, SMC |
| `experiments/asymptotics/NOTES.txt` | the N!/(κ ln N)^N conjecture, SMC to 4096 |
| `experiments/descents/PROOFS.txt` | descent and LDS bounds, SAT data |
| `experiments/independence/PROOFS.txt` | pair independence, including the one-outside-element case |
| `experiments/labelling/PROOFS.txt` | labelling / right-heavy reformulation of the descent bound, failed and surviving lemma candidates |
| `experiments/live/FINDINGS.txt` | dead and live prefixes, Beatty copies |
| `experiments/live2/PROOFS.txt` | residue chain theorem, reduction of liveness to RS + Adjacent Lemma |
| `experiments/live3/PROOFS.txt` | RS for primes (partial), the Adjacent Lemma obstruction, near classes |
| `experiments/live4/PROOFS.txt` | enlarged proven live family, uniform transfers, exceptional-class attempts |
| `experiments/adjacent/PROOFS.txt` | Theorem G and the interval / Adjacent Lemma proof |
| `docs/LITERATURE.md` | literature and OEIS survey |

## Generating valid sequences

`python3 experiments/generate/gen.py N [--mode tree|ladder|comp|slip] [--seed S] [--choices BITS] [--index i] [--verify]`
prints a valid fold sequence for any N (up to 10^6 in seconds). The default is the
truncated bit-reversal order, which is symmetric too. `--index i` gives the i-th fold in
O(log N). Modes:
- `tree`: 2^{N−1} members selected by `--choices`;
- `ladder`: O(log N) doubling steps;
- `comp`: mixed-radix residue composition;
- `slip`: N^{(1/8+o(1))N} members.

See `experiments/generate/NOTES.txt`.

## Practical note for folders

A partial semi-symmetric sequence can get stuck. For example, with N = 4, bisecting
panels 1 then 4 leaves no valid move. Two families that never get stuck:
- the "parity block" order: bisect all even panels (recursively, in a valid order for
  ⌊N/2⌋ panels), then all odd ones, or the reverse;
- when q ∣ N, the same by residue classes mod q: whole classes in the order of a valid
  q-sequence, each class internally in a valid (N/q)-order (the composition theorem).
