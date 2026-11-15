# Literature: symmetric / quasisymmetric functions, RSK, Eulerian-type polynomials

Angle: does the set `V_N` of semi-symmetric fold sequences (as permutations `a`, or as time
words `t = a^{-1}`) carry hidden algebraic structure visible through its quasisymmetric
function, its RSK data, or its statistic polynomials?  Sources actually consulted
(2026-11-15), what they say, and whether they apply.  Results of the tests are in `NOTES.txt`.

## Schur-positive ("fine") sets of permutations

- **R. Adin, Y. Roichman, *Matrices, characters and descents***, arXiv:1301.1675
  (https://ar5iv.labs.arxiv.org/html/1301.1675).  A set `B ⊆ S_n` is *fine* for a
  representation `ρ` if `χ^ρ(μ) = Σ_{π ∈ B ∩ U_μ} (-1)^{|Des π \ S(μ)|}` (sum over
  `μ`-unimodal elements) for all `μ` (Def. 1.3).  Thm 1.5(iii)/Prop. 9.3: `B` is fine iff
  `Q_B = Σ_{π∈B} F_{Des π}` is symmetric and Schur-positive.  Examples: Knuth classes and
  their unions (inverse descent classes, 321-avoiders), conjugacy classes, permutations of a
  fixed Coxeter length, arc permutations (Prop. 9.5).  Thm 7.2: for a fine set the character
  determines the whole descent-set distribution.  Question 9.4 asks which subsets are fine.
  **Applies as a test, with a negative outcome:** `Q_{V_N}` is symmetric only for `N ≤ 4`
  (both encodings), so `V_N` is not fine for any representation when `N ≥ 5`.
- **S. Elizalde, Y. Roichman, *Schur-positive sets of permutations via products of grid
  classes***, arXiv:1509.00045 (https://arxiv.org/abs/1509.00045).  General construction of
  Schur-positive sets from geometric grid classes and the product operation; explains the
  sporadic examples.  **Does not apply:** `V_N` is not a grid class and fails the symmetry
  test.  (It does resemble a *shuffle* structure: a valid sequence is a shuffle of an order
  of the left-half panels with an order of the right-half panels, see below.)
- **Z. Hamaker, B. Pawlowski, B. Sagan, *Pattern avoidance and quasisymmetric functions***,
  Algebraic Combinatorics 3 (2020) 365–388, arXiv:1810.11372 (PDF read).  `Q_n(Π) =
  Σ_{σ ∈ S_n(Π)} F_{Des σ}`; Thm 1.2 classifies `Π ⊆ S_3` with `Q_n(Π)` symmetric / Schur
  nonnegative.  Prop. 2.1: if `Q_n(Π)` is symmetric then so is `Q_n(Π^c)`, with `s_λ ↦
  s_{λ^t}`; reversal and complement are the only dihedral symmetries that preserve
  symmetry of `Q` (inverse does not, already for `Π = {132, 312}`).  Thm 3.1: `Q` of a
  shuffle of two pattern sets; Section 5: unions of Knuth classes.  **Applies:** it gave the
  test design (M-basis criterion, the role of complement / reversal, why both encodings must
  be tested separately) and the Knuth-class test.  `V_N` is closed under complement and
  reversal, which is exactly why its descent-set distribution is invariant under
  `D ↦ D^c` and under reversal of compositions.
- **J. Slattery-Holmes, *Pattern-avoiding peak functions***, arXiv:2510.17116 / EJC 33(3).
  The analogue with Stembridge's peak functions `K_Λ` and Schur `Q`-functions.  **Applies as
  a test:** the peak generating function `Σ K_{Peak(π)}` of `V_N` is not symmetric either
  (`N ≥ 5`).
- **I. Gessel, C. Reutenauer, *Counting permutations with given cycle structure and descent
  set***, JCTA 64 (1993) 189–215 (via Reutenauer's SLC precursor
  https://www.mat.univie.ac.at/~slc/opapers/s21reut.html and Elizalde–Troyka,
  arXiv:1710.05103).  The number of permutations with cycle type `λ` and descent set `D` is
  `⟨L_λ, r_D⟩` (Lie character against the ribbon); conjugacy classes are fine sets.
  **Does not apply:** `V_N` is far from a union of conjugacy classes (it is not closed under
  inverse; the cycle-type distribution is close to uniform sampling, NOTES §2).
- **R. Stanley, *Enumerative Combinatorics 2*, ch. 7** (§7.11–7.13 RSK, §7.19 Gessel's
  fundamental basis and `(P, ω)`-partitions, §7.23 Knuth equivalence).  Thm 7.19.7:
  `s_λ = Σ_{T ∈ SYT(λ)} F_{Des T}`; so a union of Knuth classes has Schur-positive `Q`.
  Cor. 7.19.5: for a labelled poset, `K_{P,ω} = Σ_{linear extensions} F_{Des}`.
  **Applies:** this is the frame for the one positive structural result: `V_N` is a union
  of commutation classes, hence `Q_{V_N}` is a sum of `K_{P,ω}` over width-2 labelled posets
  (NOTES §1.3).  RSK facts used: `P(π^r) = P(π)^t`, `P(π^{rc}) = evac P(π)`,
  `Q(π^{-1}) = P(π)`.
- **Stanley's `P`-partitions conjecture** (`K_{P,ω}` symmetric iff `(P, ω)` is a Schur
  labelled skew shape); survey: S. Billey, P. McNamara, *The contributions of Stanley to the
  fabric of symmetric and quasisymmetric functions*, arXiv:1505.01115; P. McNamara, R. Ward,
  *Equality of P-partition generating functions*, arXiv:1210.2412.  Proven when all edges are
  weak, and for `|P| ≤ 7` (Stembridge).  **Relevance:** the heaps of `V_N` are unions of two
  chains with crossing relations, not skew shapes, so no symmetry is to be expected; the
  data agree.
- **P. Cartier, D. Foata, *Problèmes combinatoires de commutation et réarrangements***
  (LNM 85, 1969) and **G. X. Viennot, *Heaps of pieces I*** (LNM 1234, 1986).  Trace monoids
  and heaps: words modulo commutation of independent letters = heaps = posets; the number of
  words of a heap is its number of linear extensions.  **Applies (new for this project in
  this form):** the commutation lemma (Lean: `swap_mem_semiSeqs`, converse
  `indep_of_swap_mem_semiSeqs`) says `V_N` is a union of trace classes for the independence
  relation "neither panel lies in the other's window".  The Möbius-inversion formula of
  Cartier–Foata counts *all* traces, not the valid ones, so it gives no formula for `a(N)`.

## Peak algebra

- **J. Stembridge, *Enriched P-partitions***, Trans. AMS 349 (1997); summary in
  Aguiar–Bergeron–Nyman arXiv:math/0508041 and Petersen arXiv:math/0512366.  Peak functions
  `K_Λ = Σ_{α : Λ ⊆ D(α) ∪ (D(α)+1)} 2^{ℓ(α)} M_α`; the descents-to-peaks map `θ(F_D) =
  K_{Peak(D)}`; peak sets of `n`-permutations number Fibonacci.  **Applies as a test** (peak
  version of the symmetry test: negative), and gives the γ-positivity mechanism
  `A(x) = ((1+x)/2)^{n-1} P(4x/(1+x)^2)` for sets invariant under valley hopping: `V_N` is
  *not* such a set (NOTES §3.3).

## Unimodality, real-rootedness, γ-positivity

- **P. Brändén, *Unimodality, log-concavity, real-rootedness and beyond***, arXiv:1410.6601
  (https://ar5iv.labs.arxiv.org/html/1410.6601).  Thm 7.3 (Borcea–Brändén) characterises
  linear operators preserving real-rootedness; Example 7.3: the Eulerian operator
  `T_n = x(1-x) d/dx + (n+1)x`; §8 interlacing families, compatible polynomials
  (Chudnovsky–Seymour), `s`-Eulerian polynomials (Savage–Visontai).  Remark 3.1: palindromic
  + real-rooted + nonnegative ⇒ γ-nonnegative.  Thm 3.2/Cor 3.3: a set invariant under the
  `Z_2^n` (modified Foata–Strehl) action has a γ-nonnegative descent polynomial.  §6:
  Neggers–Stanley conjecture (`W_{P,ω}(x) = Σ_{lin. ext.} x^{des+1}` real-rooted) is false
  in general (Brändén; Stembridge for natural labellings); true unimodality for graded
  naturally labelled posets (Reiner–Welker); sign-graded posets are γ-nonnegative (Thm 6.2).
  **Applies:** (i) the operator-recurrence search of NOTES §3.4 is the "Eulerian
  recurrence" ansatz, all negative; (ii) the descent polynomial of `V_N` is a sum of
  `W_{P,ω}` over the heaps, so its observed real-rootedness for all `N ≤ 19` is *not*
  explained by any theorem here (sums of real-rooted polynomials need a common interleaver,
  and single `W_{P,ω}` need not even be real-rooted); (iii) Remark 3.1 explains why
  γ-positivity follows from real-rootedness in our tables.
- **C. Athanasiadis, *Gamma-positivity in combinatorics and geometry***, arXiv:1711.05983
  (https://ar5iv.labs.arxiv.org/html/1711.05983).  Definition (1); Thm 2.1 (Foata–
  Schützenberger, Foata–Strehl interpretations of the γ-coefficients of `A_n`); Thm 2.7
  (Brändén: `P`-Eulerian polynomials of graded posets); §2.1.3: Gessel's conjecture on the
  two-sided Eulerian polynomial `Σ x^{des w} y^{des w^{-1}}`, proved by Lin (Thm 2.12):
  `= Σ γ_{ij} (xy)^i (x+y)^j (1+xy)^{n-1-2i-j}`.  **Applies as a test:** the joint
  polynomial `Σ_{a ∈ V_N} x^{des a} y^{des t}` is not symmetric in `x ↔ y` (the two
  marginals differ from `N = 5`), so no two-sided γ-expansion exists.
- **T. K. Petersen, *Eulerian Numbers*** (Birkhäuser 2015), chapters 1–4, 9: recurrences
  for Eulerian, Narayana and peak polynomials, real-rootedness by interlacing, γ-vectors.
  **Applies** as the catalogue of ansätze (first-order differential recurrences in `N`);
  none of them fits the data.

## Statistics on restricted permutations

- **T. Dokos, T. Dwyer, B. Johnson, B. Sagan, K. Selsor, *Permutation patterns and
  statistics***, Discrete Math. 312 (2012), arXiv:1109.4976; **B. Sagan, C. Savage,
  *Mahonian pairs***, JCTA 119 (2012).  `inv`- and `maj`-generating functions over pattern
  classes, `q`-Wilf equivalences (mostly the trivial ones from the dihedral symmetries),
  Mahonian pairs `(S, T)` with `Σ_S q^{maj} = Σ_T q^{inv}`.  **Applies as a test:** on `V_N`
  the only equidistributions among 42 classical statistics (21 per encoding) are the ones
  forced by reversal, mirror and inversion; in particular `(V_N, V_N)` is not a Mahonian
  pair (`maj` and `inv` have different distributions already at `N = 4`).

## Summary

No source gives a formula.  The symmetric-function machinery requires closure properties
(Knuth classes, conjugacy, valley hopping) that `V_N` does not have; the one structure that
is present, closure under commutation of independent panels (heaps), reduces `Q_{V_N}` to
`(P, ω)`-partition enumerators but does not make it symmetric.  The real-rootedness of the
two descent polynomials and of the peak and record polynomials is an empirical fact not
covered by the known operator or interlacing theorems.
