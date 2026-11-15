# Cross-domain campaign: ten angles of attack (2026-11-15)

Ten agents each attacked the count a(N) of semi-symmetric fold sequences from a different
field. Each read literature from its field, ran experiments, and formalized what it
proved in Lean (`Folds/Xd*.lean`, all in the core library; no `sorry`, no
`native_decide`). The shared brief is `docs/CROSS_DOMAIN_BRIEF.md`.

**Outcome: no formula and no recurrence for a(N).** Every angle ended in an explicit
obstruction. The campaign did produce one new object that four angles found
independently, an improved upper bound, and several exact theorems.

Labels: **[Lean]** machine-checked; **[paper]** proved in the notes only; **[data N ≤ n]**
checked numerically on that range; **[conj]** conjecture.

## Main findings

### 1. Swap classes (found independently by angles 4, 5, 7 and 8)

Call panels x < y *independent* if neither lies in the other's window, i.e.
2x ≤ y and x + N + 1 ≤ 2y. Independent panels lie in opposite halves.

- **Swapping is context-free [Lean].** Two adjacent steps of a valid sequence can be
  swapped, keeping validity, if and only if the two panels are independent
  (`XdTraces.swap_step_iff`, `XdOlympiad.far_swap_mem`, `XdSymFun.swap_mem_semiSeqs`).
- **Classes.** Under these swaps the valid sequences split into classes, and
  a(N) = Σ over classes of the class size [Lean: `XdTraces.semiCount_eq_sum_swapClasses`].
  The order of the left-half panels and the order of the right-half panels are class
  invariants [Lean]. That they determine the class, and that each class is an interval of
  the weak order whose size is a lattice-path count, is [paper; data N ≤ 13].
- **Equivalently [paper; data N ≤ 8]:** validity depends only on the acyclic orientation
  that a sequence induces on the "visibility graph" (x ~ y if one lies in the other's
  window), so a(N) = Σ over balanced acyclic orientations O of the number of linear
  extensions of O.
- **The class count** K(N) = 1, 1, 2, 2, 6, 12, 20, 54, 192, 412, 1312, 4746, 13926, …
  (computed to N = 28). Not in the OEIS. No P-recursive recurrence (order ≤ 7,
  degree ≤ 5). Computing it needs the same 2^N subset DP as a(N).
- **Control:** in the symmetric (3-AP-free) case the number of balanced orientations is
  2^e(N) with e(N) = e(⌈N/2⌉) + e(⌊N/2⌋) + 1 [data N ≤ 22]. This doubling recursion fails
  for the semi-symmetric case at N = 6.
- **No rigid sequences [conj; data N ≤ 22]:** every valid sequence (N ≥ 2) has two
  adjacent independent panels.
- The valid sequences form an order-convex subset of the weak order [Lean:
  `XdTraces.semiSymmetric_of_weak_between`].

So a(N) decomposes exactly over a combinatorial family, but the family is as hard to
count as a(N).

### 2. A better upper bound for all N (angle 9)

**[Lean] `XdEntropy.semiCount_le_kick`:** a(N) ≤ c!·c^(N−c) whenever
(N−c)(N−c+1) ≤ E(N), where E(N) ≈ N²/6 is the number of pairs of panels lying in each
other's windows. This gives **a(N) ≤ N!·e^{−(0.1164+o(1))N} for every N**, improving the
odd-N constant from 0.0878. (Even N keeps 0.1255 from `MaxMoves2`.)

Mechanism: placing a panel flips the window parity of every unplaced panel that sees it,
so that panel is invalid either before or after the step. Summing along the sequence, the
total shortfall of valid moves is at least E(N)/2, and weighted AM–GM converts this into
the product bound.

The entropy method proper (reveal the placement times panel by panel) provably caps out:
in any revelation order at most ⌊log₂N⌋ + 1 panels per half are revealed after their own
windows [Lean: `last_in_window_double`], which yields only e^{−Θ(log² N)}.

Room left: the true minimum shortfall is about 2.0 × E/2 for N = 20–24 [data]; if that
ratio persists, a(N) ≤ N!·e^{−0.28N} [conj].

### 3. Exact theorems that came out along the way

- **Sign balance [Lean]:** #even = #odd valid permutations when N ≡ 2, 3 (mod 4)
  (`XdOlympiad.signedCount_eq_zero`). For N ≡ 0, 1 (mod 4) the difference is small and
  irregular (2, −4, −8, −8, −116, 120, 572, …) [data N ≤ 24].
- **Imbalance-parity sum [Lean]:** Σ over all permutations of Π_m (−1)^{D_m} is 0 when
  4 ∣ N, where D_m is the left-minus-right imbalance of panel m
  (`XdConstTerm.sum_prod_neg_one_pow_D_eq_zero`).
- **Euler characteristic [Lean]:** for even N ≥ 4, Σ_k (−1)^k W(N,k) = 0, where W(N,k)
  counts ordered set partitions into k blocks in which every panel is balanced against
  the earlier blocks (`XdWeak.euler_A_even`).
- **Edge counts of the step graph [paper; data N ≤ 24]:** the number of valid steps
  (S, m) over all subsets S is N·C(N, N/2) for even N and (2N−1)·C(N−1, (N−1)/2) for odd
  N (OEIS A152548).
- **Half-line model (angle 1).** With windows [1, 2m−1] only (a strip with one end):
  panel N−c is forced to step 2c+1 [Lean: `XdIntervals.halfLine_getElem`], and
  H(2n+1) = H(n) [paper; data n ≤ 23]. An interval strictly inside a longer strip has no
  valid ordering once it is at least 2 panels from both ends [Lean:
  `intervalCount_eq_zero`].
- **Descent polynomials** of valid sequences are palindromic [Lean] and real-rooted
  [data N ≤ 19 and N ≤ 23 for the two encodings; conj for all N].
- **Discrepancy:** a "parking" condition holds for every reachable set [Lean:
  `XdWords.reachable_parking`], but it is weak (99% of all subsets satisfy it at N = 24).
- **Canonical generator:** the prefix sets of truncated bit reversal are prefixes of
  one-hole Toeplitz (period-doubling) words [Lean: `XdWords.canon_prefix_word`].

## The ten angles

| # | field | directory, Lean file | result |
|---|---|---|---|
| 1 | generating trees, kernel method, "strengthen the induction" | `xd_intervals`, `XdIntervals` | No family containing a(N) has a closed recurrence. A generating tree needs about a(N)/2 labels (one-panel deletion) [data]. Closed relation only for the half-line model, H(2n+1) = H(n), which does not contain a(N). |
| 2 | differential posets, dual graded graphs | `xd_graded`, `XdGraded` | Negative. DU − UD is never scalar or diagonal (N ≥ 3) [Lean: `comm_offdiag`]; no dual operator exists [data N ≤ 10]; the live-set poset is not Peck for 7 ≤ N ≤ 12, not a lattice, not shellable. |
| 3 | constant terms, tournaments, character sums | `xd_constterm`, `XdConstTerm` | Dropping transitivity gives balanced tournaments B(N), which stay within 6% of the independent (Wallis) model: useless as a bound. Mod-d relaxations have no recurrence. Signed-sum theorem above. |
| 4 | topological combinatorics, reciprocity | `xd_weak`, `XdWeak` | Euler-characteristic theorem above; a(N) as a sum over balanced acyclic orientations; lower columns and Möbius values as irregular as a(N). |
| 5 | partial commutation, heaps, weak order | `xd_traces`, `XdTraces` | Swap classes (finding 1). Validity is not a local weight on heaps, so Cartier–Foata inversion counts all traces (an explicit product) but not the valid ones. |
| 6 | connection matrices, tensor-network rank | `xd_rank`, `XdRank` | Negative. Parity cut rank ≥ 0.896·(N/2)! [data N ≤ 14]; residue cuts full rank; spatial middle cut ≈ (N/2)!·0.73^(N/2) [data N ≤ 17]. Ranks are computed mod a prime (lower bounds). |
| 7 | symmetric functions, RSK, Eulerian polynomials | `xd_symfun`, `XdSymFun` | Not symmetric for 5 ≤ N ≤ 12, not a union of Knuth classes; 4554 operator-recurrence searches negative; real-rootedness conjecture. |
| 8 | competition mathematics | `xd_olympiad`, `XdOlympiad` | Swap classes again; sign balance; exact effect of deleting panel 1 (no relation a(N) ↔ a(N−1)); no further invariants. |
| 9 | entropy method | `xd_entropy`, `XdEntropy` | New upper bound (finding 2); proof that panel-by-panel revelation caps out. |
| 10 | words, doubling map, origami | `xd_words`, `XdWords` | Orbit formula for the discrepancy; no discrepancy inequality separates reachable sets ([1,k] is reachable with maximal discrepancy) [Lean]; no orbit-structure signal in a(N) beyond the mod-3 effect; the counting problem was not found in the origami literature. |

Each directory is under `experiments/` and has `NOTES.txt` (results with labels) and
`LITERATURE.md`.

## Literature

Each `experiments/xd_*/LITERATURE.md` lists the sources for that field and says for each
whether it helped. **Caveat:** the agents ran under a tight usage budget. Most sources
were consulted through abstracts and search summaries, or cited from memory, and each
file marks which. Sources read in full include Freedman–Lovász–Schrijver (connection
matrices), Beck–Sanyal (reciprocity), Banderier et al. (generating trees, first pages),
Stanley's sign-balanced posets paper, and the Kvant/All-Union 1974 problem that is the
symmetric case. `xd_traces` and `xd_entropy` were written entirely from memory.

Fields surveyed: generating trees and the kernel method; differential posets and dual
graded graphs; constant-term identities and tournament counting; combinatorial
reciprocity and discrete Morse theory; trace monoids and heaps; graph-limit connection
matrices and matrix-product states; quasisymmetric functions and RSK; olympiad
combinatorics; the entropy method; Sturmian and Toeplitz words, doubling-map dynamics
and origami mathematics.

## Why nothing closed: the common obstruction

The angles fail for one reason seen from different sides. The windows of the left-half
panels are nested prefixes, and those of the right half nested suffixes, so every panel
interacts with a constant fraction of the others. Consequently:

- no deletion or insertion map is well defined (angle 1), and no cut has small rank
  (angle 6);
- commutation is too rare to help: only cross-half pairs commute, and at most two panels
  commute pairwise (angles 5, 8);
- relaxations that restore a product structure discard exactly the correlations that
  matter (angle 3), and the graded graph has no operator relation (angle 2);
- the set of valid permutations has no symmetric-function or Knuth-class structure
  (angle 7).

## Open leads from this campaign

1. Prove that no valid sequence is rigid (every valid sequence has an adjacent
   independent pair).
2. Improve the shortfall bound E(N)/2 towards the observed ≈ E(N): this would give
   a(N) ≤ N!·e^{−0.28N}.
3. Prove real-rootedness of the descent polynomials.
4. Formalize the (left order, right order) classification of swap classes and
   H(2n+1) = H(n).
5. Find any formula for K(N).
