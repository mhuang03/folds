# Literature: differential posets, dual graded graphs, sl₂-posets

What was read, what it says, and whether it applies to the graded graph Γ_N of
semi-symmetric steps (vertices: subsets of [N]; a(N) = number of maximal chains).
Sources marked (abstract) were only read through their abstract page or a search
summary; the others through the full text or a detailed rendering. The journal references
of items 3, 6, 8 and 13 are quoted from memory (the arXiv pages fetched do not list them);
the product formula in item 2 is a one-line computation from the relation, not a quotation.

## Differential posets

1. **R. P. Stanley, "Differential posets", J. Amer. Math. Soc. 1 (1988), 919–961.**
   <https://www.ams.org/jams/1988-01-04/S0894-0347-1988-0941434-9/> (abstract; content via
   <https://en.wikipedia.org/wiki/Differential_poset> and Lenart's survey, item 7).
   A graded poset with 0̂ is r-differential iff DU − UD = rI. Consequences: Σ_{rank n} e(x)² =
   rⁿ n!, closed walks 0̂→0̂ of length 2n number (2n−1)!!·rⁿ, the number of upward paths has
   e.g.f. e^{rx+x²/2}, the eigenvalues of DU are integers, rank sizes increase.
   *Applies?* No. In Γ_N the commutator is not scalar and not even diagonal (Lean:
   `comm_offdiag`, all N ≥ 3). The analogue of Σe² is Q(N,k) = Σ_{|S|=k} g(S)², which has
   no closed form and no OEIS match (NOTES §6).

2. **R. P. Stanley, "Variations on differential posets", in Invariant Theory and Tableaux,
   IMA Vol. Math. Appl. 19 (1990), 145–165** (abstract; statement taken from Fulman, item 6,
   and Lenart, item 7). Sequentially differential posets: D_{n+1}U_n − U_{n−1}D_n = r_n I
   with r_n depending on the rank; then Σ_{rank n} e(x)e′(x) = ∏_{j≤n}(r_0+…+r_{j−1}). The
   Boolean lattice B_N is the model finite case with r_k = N − 2k (an sl₂-representation).
   *Applies?* This is the natural target for a finite self-dual graph such as Γ_N. Tested as
   a linear feasibility problem for the lowering operator (NOTES §5): no solution supported
   on Boolean covers or on the edges for 3 ≤ N ≤ 10; with an arbitrary (non-local) D′ the
   achievable r are exactly the trivial ones coming from invertible chain matrices.

3. **A. Miller, V. Reiner, "Differential posets and Smith normal forms", arXiv:0811.1983
   (Order 26 (2009))** (abstract). Conjecture: DU + tI and UD + tI have Smith normal forms
   over ℤ[t] for every r-differential poset; proven for the Young–Fibonacci lattices,
   checked for Young's lattice.
   *Applies?* Tested the analogous statement: Smith forms of U_k and D U for Γ_N are
   unstructured (one huge last invariant factor, NOTES §3). Negative.

4. **A. Miller, "Differential posets have strict rank growth: a conjecture of Stanley",
   arXiv:1202.3006** (abstract); **R. P. Stanley, F. Zanello, "On the rank function of a
   differential poset", arXiv:1111.4371** (abstract). Rank sizes of differential posets grow
   strictly; bounds between p(n) and Fibonacci numbers.
   *Applies?* Only by analogy: the rank sizes of the live poset are symmetric and (data
   N ≤ 24) unimodal, but the usual proof (injectivity of U) fails here.

## Dual graded graphs and Schensted-type correspondences

5. **S. Fomin, "Duality of graded graphs", J. Algebraic Combin. 3 (1994), 357–404;
   "Schensted algorithms for dual graded graphs", J. Algebraic Combin. 4 (1995), 5–45.**
   <https://emis.muni.cz/journals/JACO/Volume3_4/bx4c3m5xlcdmtgu3.html>,
   <https://www.maths.tcd.ie/EMIS/journals/JACO/Volume4_1/j3330612tm0w1m47.html> (abstracts;
   the EMIS full texts were unavailable (HTTP 503), content via Nzeutchap, item 9, and Lam,
   item 8). Two graded graphs (Γ₁, Γ₂) on the same ranked vertex set are r-dual iff
   D₂U₁ − U₁D₂ = rI (more generally D_{n+1}U_n = q_n U_{n−1}D_n + r_n I). Then pairs (path in
   Γ₁, path in Γ₂) with the same endpoint of rank n are in bijection with r-coloured
   permutations (growth diagrams, generalised Robinson–Schensted), Σ e₁(x)e₂(x) = rⁿ n!.
   *Applies?* This is the precise form of task 3 ("find a second graph Γ′"). The search
   for Γ′ (edges on Boolean covers, arbitrary real weights, so also any weighting by the
   imbalance and the graph of the relaxed problem) has only the zero solution for
   3 ≤ N ≤ 10. Note also that a dual pair would give Σ g(S)e′(S) = ∏(partial sums of r),
   which is information about a weighted sum over one rank, not about a(N) = g([N]).

6. **J. Fulman, "Commutation relations and Markov chains", arXiv:0712.1375 (Probab. Theory
   Related Fields 144 (2009))** (abstract and search summary). Uses D_{n+1}U_n =
   a_n U_{n−1}D_n + b_n I to diagonalise down-up Markov chains.
   *Applies?* Would give the spectrum of the "add a valid panel, remove a valid panel"
   chain on rank k; the relation fails (DU ∉ span(UD, I), NOTES §5c), and the spectrum of DU
   is not integral.

7. **C. Lenart, "Combinatorial representation theory of Lie algebras. Richard Stanley's work
   and the way it was continued", arXiv:1406.0352** (full text read, §3). States the
   definitions used here: a ranked poset is *Peck* if it is rank-symmetric, rank-unimodal
   and strongly Sperner; an *sl₂-poset* has an order-raising X (Xx = Σ_{y ⋗ x} c_{xy} y) and
   a lowering Y with (XY − YX)_i = (2i − n) Id_i; **Theorem 3.3 (Proctor; Stanley): a ranked
   poset is Peck iff it is an sl₂-poset.** Also the definition of r-differential posets and
   the pointer to down-up algebras.
   *Applies?* Yes, as the decisive test. The poset L_N of live sets is rank-symmetric and
   (data) unimodal, but it is not Peck for N = 3 and 7 ≤ N ≤ 12: no weighted up operator is
   injective below the middle (Lean: `twins_three`, `twins_nine`), and the Sperner property
   fails for 7 ≤ N ≤ 12.

8. **T. Lam, "Quantized dual graded graphs", arXiv:0808.0345 (Electron. J. Combin. 17
   (2010))** (full text via <https://ar5iv.labs.arxiv.org/html/0808.0345>). Weights in ℕ[q];
   relation D′U − qUD′ = rI; then Σ_v f^v f′^v = rⁿ [n]_q!; q = −1 gives signed differential
   posets. Examples: Fibonacci, permutations (weight q^{n−s}), tableaux, plane binary
   trees; open problem: quantize Young's lattice.
   *Applies?* The permutation example is the closest in spirit (vertices = permutations,
   edges = insert the next value), but there every insertion is allowed. Tested
   D′U − qUD′ = r_k I for q = −1, 2, 3 with D′ on Boolean covers or on edges: only D′ = 0
   (3 ≤ N ≤ 9).

9. **J. Nzeutchap, "Dual graded graphs and Fomin's r-correspondences associated to the Hopf
   algebras of planar binary trees, quasi-symmetric functions and noncommutative symmetric
   functions", FPSAC 2006.** <https://fpsac-archive.github.io/FPSAC06/SITE06/papers/53.pdf>
   (full text, introduction). Dual graded graphs arise from pairs of dual graded Hopf
   algebras (multiplication by the degree-1 generator on one side, its adjoint on the other);
   the sylvester and hypoplactic congruences are r-correspondences.
   *Applies?* It suggests looking for a Hopf-algebra (or tower-of-algebras) structure whose
   branching graph is Γ_N. Γ_N depends on N (the window of m changes with N), so there is
   no single infinite graded graph containing all Γ_N as intervals; no such structure found.

10. **R. Patrias, P. Pylyavskyy, "Dual filtered graphs", arXiv:1410.7683 (Algebraic
    Combinatorics 1 (2018), 441–500)** (abstract). K-theoretic analogue: DU − UD = D + I,
    Möbius and Pieri constructions.
    *Applies?* Needs up-edges that stay in the same rank (filtered, not graded); Γ_N has no
    natural such edges. The Möbius construction starts from an existing dual graded graph,
    which we do not have. Not applicable.

## sl₂-actions, Sperner property, down-up algebras

11. **R. Proctor, "Representations of sl(2,ℂ) on posets and the Sperner property", SIAM J.
    Algebraic Discrete Methods 3 (1982), 275–280** (statement via item 7).
    Peck ⟺ sl₂-poset. Used as in item 7.

12. **C. Gaetz, Y. Gao, "A combinatorial sl₂-action and the Sperner property for the weak
    order", Proc. Amer. Math. Soc. 148 (2020), 1–7, arXiv:1811.05501** (abstract). The weak
    order on S_n is Peck, by an explicit weighted order-raising operator.
    *Applies?* A model for the kind of result one could hope for (a(N) counts permutations,
    and L_N is a subposet-like object of the Boolean lattice); the twin obstruction shows no
    such weighting exists for L_N.

13. **G. Benkart, T. Roby, "Down-up algebras", J. Algebra 209 (1998), 305–344,
    arXiv:math/9803159** (abstract; relations from item 7 and the standard definition
    D²U = αDUD + βUD² + γD, DU² = αUDU + βU²D + γU). Satisfied by differential posets
    (α = 2, β = −1, γ = 0) and by q-analogues.
    *Applies?* Tested: D²U ∉ span(DUD, UD², D) at every rank for 5 ≤ N ≤ 9. Negative.

## OEIS

- A152548 (1, 4, 10, 24, 54, 120, 260, 560, …) = number of edges of Γ_N
  (= N·C(N, N/2) for even N, (2N−1)·C(N−1, (N−1)/2) for odd N).
- A156040 = number of 2-sets that can be entered in both orders (N ≥ 2).
- No match: numbers of live sets, reachable sets, live sets at the middle rank,
  Σ g(S)² (per rank, middle rank, total), Σ_S g(S), |μ(0̂,1̂)|, live 3-sets.

## Verdict

The whole toolbox rests on a commutation relation between U and a lowering operator.
For Γ_N every version tested fails, and for the live poset there is a rank-level
obstruction (non-injectivity of every weighted U below the middle) that rules out sl₂ /
Peck structures outright. The field contributes definitions, exact bookkeeping identities
(self-duality, adjointness, trace of the commutator, edge counts) and a clear negative
answer, but no formula for a(N).
