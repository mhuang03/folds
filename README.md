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
| closed form for a(N) | **none found; very unlikely**. A systematic search (`experiments/recsearch/REPORT.txt`) found **no recurrence in previous terms**: P-recursive up to 30 unknowns (LLL up to 64), divide-and-conquer, convolution, algebraic and ODE generating functions, OEIS transforms, mod-p, and about 10⁶ expression trees. The OGF is provably not algebraic. a(N) is not P-recursive if the growth conjecture holds. A second search (`experiments/recsearch2/REPORT.txt`, about 14,200 boxes) also excludes Somos/Riccati/cubic shift relations, Mahler and q-difference equations, Bell-type exponential-coefficient ODEs (per parity), Hankel and continued-fraction structure, 2-regularity and automaticity. The prefix-count bivariate generating function is provably not D-finite. No OEIS match; huge prime factors; no holonomic recurrence; even the symmetric analogue A003407 has no known formula (and, per Ho 2026, no exponential growth rate) |
| recursive formula | **proven** (Lean): subset recursion `g`, and a(N) = Σ_{\|S\|=k} g(S)·g(Sᶜ) for every k |
| terms | a(1..38) exact; ln a(N) estimated to N = 4096 |
| exact formulas for pieces | T(N,2) = ⌊N²/2⌋ and the period-6 quasi-polynomial T(N,3) (**proven in Lean**). **Exact** quasi-polynomials for T(N,4), T(N,5) and T(N,6), with periods 168, 1680 and 104160, derived from Ehrhart generating functions. The period of T(N,7) is 624960. Single-panel Wallis count (**proven**) |
| congruences | a(N) ≡ c(N) (mod 4) (**proven**); 4 ∣ a(N) for N ≡ 3 (mod 4) (**proven**); no patterns modulo odd primes |
| growth | **rigorously (N/4096)^{N/16} ≤ a(N) ≤ N!·e^{−0.0878N(1+o(1))} (e^{−0.1255N} for even N)** (super-exponential lower bound, proven in Lean; a(N) ≥ (N/2)^{N/6} for N = 2^L). **Conjecture:** a(N) = N!/(κ ln N)^N |
| arithmetic effect | multiples of 3 sit above trend (all N ≤ 33). Mechanism: the 2-cycle {N/3, 2N/3} of the doubling map |

Here T(N,k) is the number of valid k-step prefixes, and c(N) is the number of sequences
fixed by reversal∘mirror.

## Data

`experiments/semi_counts.txt`: N ≤ 27 come from `experiments/semi.c`; N = 28..38 come
from the Rust crate `rust/`.

a(1..38) = 1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328,
9167908, 47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
2505681033958, 18168130281086, 119006527671252, 979730153850974,
6564449510287388, 55581983250573500, 413109755332919448, 3603074636066234798,
27545080998591561856, 262878496654501774250, 2037247307316034896720,
20222490725552617395966, 171668579369815966705184, 1711977358970374039688092,
14916356465581456801127844, 162918548122441960881265188, 1435459602925600924848243286,
15884954204816776206921874682.

- The symmetric counts are OEIS A003407 (3-AP-free permutations).
- c(N), for sequences fixed by reversal∘mirror, is known to N = 41
  (`experiments/arith/`).
- `rust/` uses a mirror-orbit, meet-in-the-middle layered DP: a(33) takes 74 s. a(36) and a(37) used block streaming (6.2 and 11.2 GB
  peak) and 13 u8 CRT residues each (2.6 h and 4.6 h). a(38) used finer sub-blocks plus disk spill (`--sub 4`, 4 GB RAM, ≤ 13.4 GB disk, 4.6 h). N = 39 needs about 36 GB of RAM+disk (see `rust/README.md`).

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

Build with `lake exe cache get && lake build` (the fast core library `Folds`, a few
minutes; this is what CI checks on every push). The certificate-heavy modules (the
ThinCover kernel checks, the LRAT certificates, per-N witness tables: Live3p–Live3t, Live7,
Live8, ArithCover, Residual, CoverAll, ThinCover*, LabellingSAT4*, SymRun) form the separate
library `FoldsCerts`. Build it with `lake build FoldsCerts` (about an hour; build the
`ThinCoverKernel*` and `LabellingSAT4Certs*` modules one at a time on machines under
16 GB). It is checked by the `certs` workflow on demand, weekly, and when those files
change. There is no `sorry` and no
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
| `LabellingSAT*` (M) | kernel-checked LRAT certificates (own sound checker, no `ofReduceBool`): the labelling bound for t = 3, 4 for **all N**, hence des + 1 ≥ min(⌊log₂(N+1)⌋, 5) and the same for LDS |
| `Live5` (M) | `coReach_one_N`: {1,N} is co-reachable for every odd N ≠ 7; transfers through Beatty copies and splits; family `Cov5` (every non-dead 2-set for N = 100 and 130) |
| `RecCount` (M) | `card_parFam`: the recursive parity family has 2^{N−1} members; `g_winEmb`: g(X) = a(\|X\|) for window copies; antichain decomposition `semiCount_eq_sum_antichain`; a(N) = 2a(⌊N/2⌋)a(⌈N/2⌉) + 2a(jn)a((j+1)n) + rest |
| `Neutral` (M) | **classification of neutral sets** (`neutral_classification`: only the parity classes and E_d, E_dᶜ for odd d ∣ N); **identity (A)** in full (`identity_A`); J(k) universality and **identity (B)** (`identity_B`) |
| `Upper` (M) | odd-N parity upper bound `semiCount_odd_le_prod` (a(N) ≤ N!·e^{−0.059N(1+o(1))}), so there is now an exponential saving for **all** N; the discrepancy transfer `disc_le_of_cycDefect_le` |
| `PathLemma` (M) | the reduction `PathLemma.eventually_le` (Path Lemma ⇒ a(N) ≤ N!·e^{−ω(N)}); linear variant; the cyclic-defect step identity and the run bound on valid moves |
| `Live6` (M) | swapped Beatty copies (`coReach_three`: {3,N−3} for N ≥ 37); the {1,4,6,…,N} copy (`coReach_one_half`); `Cov6`; **reduction** `extends_iff_not_dead`: the full liveness iff follows from one arithmetic covering lemma |
| `MaxMoves` (M) | `card_moves_two_mod_four`: \|S\| ≡ 2 (mod 4) ⇒ at most ⌊2N/3⌋ valid moves (the conjectured ⌈2N/3⌉ for all even \|S\| is **false**: `moves_sixty`); improved upper bounds a(N) ≤ N!·e^{−0.1146N} (even N) and e^{−0.0769N} (odd N) |
| `MaxMoves2` (M) | 2-adic valid-move bound `card_moves_two_adic` ((a+2)V ≤ (a+1)N for \|S\| = 2^a·odd) and its sharper version with an \|S\| term; upper bounds a(N) ≤ N!·e^{−0.1255N} (even) / e^{−0.0878N} (odd) |
| `SuperExp4` (M) | upper odd slip positions + reversal averaging; `self_pow_le_semiCount_pow_17`: N^N ≤ 2^{11N}·a(N)^{17} for all N ≥ 1 |
| `Live7` (M) | centred Beatty copies Z(N,p) = {⌊k(N+2)/(p+1)⌋}; {3,N−2}, {5,N−4} co-reachable; 65 witness orderings via the bitmask checker; **Conjecture C proven for every N ≤ 64** (`extends_iff_not_dead_le_64`); for N ≥ 65 it reduces to `CoverAt E7 N` (checked to N = 2665) |
| `SuperExp5` (M) | odd-N slip lemma `oddSlip_mem_semiSeqs` (with the wrap condition); odd-node gain; `self_pow_le_semiCount_pow_16`: N^N ≤ 2^{12N}·a(N)^{16} for all N ≥ 1 |
| `Copies2` (M) | copies larger than N/2 are neutral (`copy_large_neutral`); which copy sizes occur (`copies_nonempty_iff`); ⌊(N²+2)/6⌋ copies of size 2; half-size copies; explicit tail of identity (B) (`identity_B_split`) |
| `Live8` (M) | **Conjecture C proven for every N ≤ 300** (`extends_iff_not_dead_le_300`); for all N it holds modulo the purely arithmetic `ArithCover N` for N > 300 (`conjectureC_of_arith`), checked to N = 3000. Same-parity pairs and several families are settled for all N |
| `ArithCover` (M) | two-class slide (Theorem B): the near-boundary crux `dirAny_nearBoundary` for all N ≥ 301; five proven regions; `conjectureC_of_residual` reduces Conjecture C to a smaller `Residual N` (about 40% of mixed wide pairs: the near-diagonal wedge and the corner) |
| `Residual` (M) | lattice-parallelogram and slice lemmas; regions `RegionPF`, `RegionSL`, `RegionS`; `conjectureC_of_coverAll`: Conjecture C for all N follows from the semialgebraic covering statement `CoverAll N` (N > 300), which has an empty residual for 301 ≤ N ≤ 3000 |
| `CoverAll` (M) | **the whole 2-D bulk** of the pair triangle for all N ≥ 301 (`bulk`, three cells, 11 LP-certified leaves); `d1_line`; `conjectureC_of_thinCover`: Conjecture C for all N reduces to `ThinCover`, a statement about lines with bounded offsets and a bounded box |
| `Structure2` (M) | refined-count identities: L(N,m) = F(N,m) (reversal), mirror symmetry, exactly a(N)/2 sequences start with an odd panel for even N |
| `ThinCover*` (M) | **Conjecture C for all N** (`ThinCover.conjectureC`): a valid 2-prefix extends to a full semi-symmetric sequence iff it is not one of the explicit dead pairs. Built from slice and parallelogram certificates (LP-certified polynomial inequalities) for N ≥ 1000, plus 699 kernel checks for 301 ≤ N < 1000 |
| `SymParity` (M) | symmetric (3-AP-free) case: exactly half the sequences start with an odd panel (`two_mul_card_head_odd`; first and last panels always differ in parity); the same at step k when 4k ≤ N+1 (`two_mul_card_getElem_odd`, via the orientation theorem `orient`) |
| `SymStructure` (M) | symmetric case: **merge theorem** (`merge_iff_apFree`): 3-AP-free ⇔ both parity subsequences are 3-AP-free and the D-entry comes first on every linked pair; `parity_sort` |
| `Live3p` (M) | 3-prefix liveness: **iff for every N ≤ 30, N ≠ 7** (`extends3_iff_le_30`); dead 3-sets proven dead for all N; Theorem G for 3-sets in closed form (`F3S`, `coReach3_of_F`) |
| `SymStructure2` (M) | symmetric case: recursive extension test **Theorem E** (`ext_iff_cond`, decidable via `extB`), prefix-count recursion **Theorem L** (`live_rec`; L_k(N) = O(N)), exact shuffle-count identity for θ(N), and **Sharma's bound for all N** (`ends_parity`: a[k] has a[0]'s parity whenever k+6 < N/2; sharp at N = 26) |
| `PeriodLaw` (M) | arithmetic bookkeeping for the period-law exactness proofs (closed-form weights never vanish) |
| `SymRun` (M) | symmetric case: the **exact minimal opening parity run** f(N) for all N ≥ 36 (`fRun_block`: δ = ⌊N/2⌋ − f ∈ {4,5,6} by an explicit dyadic block pattern); Sharma's bound is attained exactly at the δ = 6 points (`fRun_eq_sub_six_iff`) |
| `Live3q` (M) | 3-prefix liveness iff for **every N ≤ 50**, N ≠ 7 (`extends3_iff_le_50`); for all N it reduces to `Residual3 N` (N > 50) through transfers and step families |
| `SymRatio` (M) | symmetric case: **locality** (`card_shuffles_eq_win`): the number of shuffles depends only on the last 6 entries of σ and the first 6 of τ; θ(N) as a bilinear form in 6-window laws; an exact halving recursion for the window counts |
| `Live3r` (M) | near copies (`coReach_nearEmb`); {1,2k,N} for odd N and {1,2,c} for N ≡ 1 (mod 4), c odd, settled for all N; new decidable transfer rules; reduction of 3-prefix liveness to `Residual3R` (only {1,2,c}-type sets remain: 86 triples for N = 51..70) |
| `Live3s`, `Live3Final` (M) | moved-panel copies settle four more {1,2,c} families for all N; `extends3_iff_of_residual3T`: 3-prefix liveness for all N ≠ 7 follows from `Residual3T` (N > 50) |
| `Live3t` (M) | closed-form {1,3,N} (N ≡ 1 mod 4), {1,b,N} for all b (N ≡ 2 mod 4), {1,2,N} (N ≡ 4 mod 8); reduction to `Residual3U` |
| `LiveK` | liveness for **any prefix length k**: every subset of the middle third is co-reachable (`coReach_middle`); compact, dyadic, sparse and anchored families (`CovK`); every valid prefix whose set is in them is live; halving prefixes are valid and live |
| `Ek` (M) | **E_k is false for k ≥ 5**: anchored dead families B_a (`not_coReach_anchor`; dead (2a+1)-sets inside [a, N−a]); end-panel lemmas; counting corollary `card_dead_le` (conditional) and `card_dead_pairs_le_64` |
| `Live` (M) | every first panel extends to a full sequence; every dead 2- and 3-prefix is proven dead |

## Conjectures and open problems

1. **Asymptotics.** a(N) = N!/(κ_N ln N)^N, i.e. ln a = N ln N − N ln ln N − O(N).
   Evidence: debiased SMC to N = 4096 and a Feynman–Kac model; see
   `experiments/asymptotics/NOTES.txt`. Rigorously 1/16 ≤ liminf ln a/(N ln N), and
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
   - **Exact full periods** of T(N,8) = B(8) = 158739840 and T(N,9) = B(9) = 5397154560.
     Theorem D1 (c_1, every m) and Theorem D2 (c_2, m ≤ 19) are proven on paper; see
     `experiments/periods3/PROOFS.txt`. Components from shorter cycles for k > m are open.
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
5. **Liveness (Conjecture C) — now a theorem (Lean, `Folds.ThinCover.conjectureC`).** A valid
   2-prefix [m₁, m₂] can be completed to a full semi-symmetric sequence iff it is not
   {1,N} for even N ≥ 4 or {1,7} at N = 7. For 3-prefixes the classification is proven for
   N ≤ 50 (Lean) and checked to N = 63; all N is open (`experiments/live3p/PROOFS.txt`).

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
| `experiments/live5/PROOFS.txt` | {1,N} for odd N, Beatty and split transfers, remaining corner families |
| `experiments/reccount/NOTES.txt` | exact recursions for constructible families (R1, R2, R2c, R3), neutral sets, decomposition identities (A) and (B) for a(N) |
| `experiments/labelling_lrat/NOTES.txt` | LRAT certificate pipeline and costs |
| `experiments/recsearch/REPORT.txt` | search for recurrences in previous terms (all negative), with the proven and conditional non-D-finiteness arguments |
| `experiments/neutral/PROOFS.txt` | neutral-set classification, identities (A) and (B) |
| `experiments/upper/PROOFS.txt` | upper-bound attempts; reduction of a(N) ≤ N!e^{−ω(N)} to a "Path Lemma" (numerically true); why state statistics cannot work |
| `experiments/pathlemma/PROOFS.txt` | Path Lemma attempts: the potential identity, minimiser structure, open sub-problems |
| `experiments/live6/PROOFS.txt` | swapped Beatty copies, the covering reduction for Conjecture C |
| `experiments/maxmoves/PROOFS.txt` | maximum number of valid moves, the 2-adic bound, upper-bound constants |
| `experiments/maxmoves2/NOTES.txt` | 2-adic bound, continuum maxima of V/N by \|S\|, constants |
| `experiments/superexp4/PROOFS.txt` | all-N exponent 1/17; why odd N has no free slips; truncation fails for slip chains |
| `experiments/live7/PROOFS.txt` | centred Beatty copies, the covering statement and its partial proof |
| `experiments/superexp5/PROOFS.txt` | odd-N slip lemma, exponent 1/16, the binding constraints (limit about 1/15.2) |
| `experiments/jseq/NOTES.txt` | J(N) to 33, I(N) to 38, copy counts, the J/a limit, the renewal form of (B) |
| `experiments/live8/PROOFS.txt` | Conjecture C to N = 300, the reduction to ArithCover, the route to a proof |
| `experiments/arithcover/PROOFS.txt` | Theorem B, regions, the residual and the route via three-gap / lattice flatness |
| `experiments/residual/PROOFS.txt` | lattice and slice regions, the reduction to CoverAll, the cell decomposition |
| `experiments/coverall/PROOFS.txt` | bulk cell decomposition and certificates, the remaining thin sets and their slices |
| `experiments/structure2/FINDINGS.txt` | refined counts (none nicer than a(N)), the first-panel limit law (density ∝ √min(x,1−x)), the parity offset in growth, factorisations, 1838 failed cross-sequence searches |
| `docs/RECURRENCE_LITERATURE.md` | which recurrence classes are compatible with N!/(log N)^N growth; prioritised ansätze |
| `experiments/recsearch2/REPORT.txt` | niche recurrence search (all negative), with proofs that OGF-Mahler and 2-regular forms are impossible |
| `experiments/thincover/PROOFS.txt` | the final thin-set certificates and kernel checks completing Conjecture C |
| `experiments/symstruct/PROOFS.txt` | 3-AP-free structure: an exact merge-count identity for θ(n), the prefix-extension test, Sharma's ⌊N/2⌋−6 bound for all N (sharp), the dyadic pattern of the opening run, L_k(N) recursion, log-periodic ratio θ(n)/(2θθ) |
| `experiments/live3p/PROOFS.txt` | 3-prefix liveness: the classification to N = 44, Theorem G for 3-sets, the route to all N |
| `experiments/periods3/PROOFS.txt` | period-law exactness: Theorems D1/D2, exact periods of T(N,8), T(N,9), non-simple vertices |
| `experiments/symrun/PROOFS.txt` | proof of the dyadic opening-run formula (Conjecture F′) via the φ/ψ halving states |
| `experiments/live3q/PROOFS.txt` | 3-prefix liveness to N = 50, the residual families ({1,2,c}, {1,2k,N}, corner pairs + a middle point) |
| `experiments/symratio/PROOFS.txt` | 3-AP-free: locality, an O(n³) algorithm for θ(n), **new terms θ(201..300)** beyond the OEIS b-file (`data/theta_exact.txt`), the refined Conjecture R′ (4^{−j} convergence; super-geometric when 3 ∣ x) |
| `experiments/thetaext/` | **exact A003407 θ(n) for all n ≤ 2000** (`b003407.txt`; the OEIS b-file stops at 200) via an O(n³) window/trie algorithm with 45-prime CRT; r(n) and the Conjecture R′ evidence |
| `experiments/live3r/PROOFS.txt` | near-copy transfers; the only remaining 3-prefix family {1,2,c} and its halving-chain completions |
| `experiments/fastalg/NOTES.txt` | no fundamentally faster algorithm for a(N): any time-ordered automaton needs one state per live set (proven); the exact bisimulation quotient only saves a constant factor; the trace lemma and normal form (≈16 GB for N = 39, not built) |
| `experiments/live3s/PROOFS.txt` | {1,2,c} families, why the halving chain alone cannot finish, and what remains of Residual3T |
| `experiments/live3t/PROOFS.txt` | 3-prefix residual computed to N = 150 (only {1,2,c}-type sets remain); why the copy-size p is not omega-friendly |
| `experiments/livek/PROOFS.txt` | general-k liveness families, Conjecture E_k (k-sets avoiding 1 and N are co-reachable; one exception), dead k-prefixes ~ Θ(N^{k−2}) |
| `experiments/ek/PROOFS.txt` | E_k counterexamples, the revised conjecture E*_k (radius c_k = max(1,⌊(k−1)/2⌋), exception S_{k/2} at N = 3k), checks for k ≤ 8 |
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

## Recursive count formulas from constructions

See `experiments/reccount/NOTES.txt`.
- Every constructible family has an exact recursion. For example, R1(N) = 2^{N−1} (Lean), and R2(N) = P(N) + Σ_{q|N} P(q)·R2(N/q)^q. But these families are a vanishing share of a(N).
- **Identity (A):** a(N) = 2a(⌊N/2⌋)a(⌈N/2⌉) + 2Σ_{odd d|N, 3≤d<N} a(jN/d)a((j+1)N/d) + I(N), with j = (d−1)/2. It comes from the "neutral" sets: the parity classes and the doubling-split sets E_d.
  - **Proven in Lean** (`Neutral.identity_A`), including the classification of neutral sets.
  - The remainder I(N)/a(N) → 1 (0.999 at N = 24).
- **Identity (B):** a(N) = J(N) + Σ_k J(k)·C_N(k), split by the first prefix that is a window copy.
  - J(N)/a(N) stays near 0.18.
  - **Proven in Lean** (`Neutral.identity_B`), including J(k) universality; the k > N/2 terms are explicit (`Copies2.identity_B_split`).
  - J(N) is known to N = 33. **Conjecture:** J(N)/a(N) → ρ ≈ 0.1836, with the same mod-6 effect as a(N). See `experiments/jseq/NOTES.txt`.
  - C_N(k) involves completion counts, not values of a, so it is not a closed recursion.

## Practical note for folders

A partial semi-symmetric sequence can get stuck. For example, with N = 4, bisecting
panels 1 then 4 leaves no valid move. Two families that never get stuck:
- the "parity block" order: bisect all even panels (recursively, in a valid order for
  ⌊N/2⌋ panels), then all odd ones, or the reverse;
- when q ∣ N, the same by residue classes mod q: whole classes in the order of a valid
  q-sequence, each class internally in a valid (N/q)-order (the composition theorem).
