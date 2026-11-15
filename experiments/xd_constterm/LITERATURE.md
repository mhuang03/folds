# Literature for the constant-term / tournament / character-sum angle

How each source was consulted is stated per entry: **read** (the text itself, at least the
relevant pages), **abstract** (abstract or a summary page only), **not accessed** (cited from
the field's common knowledge; the session's web quota ran out before it could be opened).
Nothing below is quoted from a source that was not opened.

## Constant-term identities

1. **G. Károlyi, Z. L. Nagy, "A simple proof of the Zeilberger–Bressoud q-Dyson theorem"**,
   arXiv:1211.6484 (https://arxiv.org/abs/1211.6484). *Read (ar5iv HTML).*
   Dyson: CT ∏_{i≠j}(1 − x_i/x_j)^{a_i} = (a_1+…+a_n)!/∏a_i!. Proof by the effective
   Combinatorial Nullstellensatz (Lasoń; Karasev–Petrov): the wanted coefficient of a
   polynomial F of degree ≤ Σd_i equals Σ over a grid A_1×…×A_n of F(c)/∏φ_i'(c_i); the
   pairwise product makes F vanish at all grid points but one.
   **Applies?** No. The method needs (i) a product over all pairs with the *same* shape of
   factor and (ii) a grid on which the product vanishes almost everywhere. Our tournament
   product ∏_{x<y}(z_y^{c_xy} + z_x^{-d_xy}) has factors that are sums of two monomials in
   *different* variables with exponents 0/1 depending on the window relation; no grid of
   size r_m+1 per variable kills it (the answer B(N) has large prime factors, NOTES 1c). And
   a(N) itself is not a product over pairs at all (transitivity is a 3-body condition).

2. **I. Gessel, G. Xin, "A short proof of the Zeilberger–Bressoud q-Dyson theorem"**,
   arXiv:math/0412339 (https://arxiv.org/abs/math/0412339). *Abstract only.*
   Formal Laurent series proof (the constant term as a polynomial in a parameter, determined
   by enough vanishing points). **Applies?** Not directly: there is no free exponent
   parameter in our product; the window radii are fixed by N.

3. **Dyson conjecture, Good's proof, Macdonald's generalisations** — Wikipedia,
   https://en.wikipedia.org/wiki/Dyson_conjecture. *Read.* Good's proof uses the recursion
   F(a_1..a_n) = Σ_i F(a_1,..,a_i−1,..,a_n). Macdonald: root-system versions, proved by
   Cherednik; type BC ↔ Selberg/Morris. **Applies?** The recursion "lower one exponent" is
   formally like the subset recursion g(S) = Σ_m g(S∖m), which we already have; but Good's
   recursion closes on n integers while ours needs the whole set S. Morris/Aomoto/Selberg
   identities (*not accessed*) concern products ∏(1−x_i)^a ∏(1−x_i/x_j)^k with uniform
   exponents; nothing window-dependent.

4. **D. Bressoud, I. Goulden, "Constant term identities extending the q-Dyson theorem"**,
   Trans. AMS 291 (1985) (https://www.ams.org/tran/1985-291-01/S0002-9947-1985-0797055-8/).
   *Abstract via search result (the AMS page refused the fetch).* Master theorem: the constant
   term of the q-Dyson-type product taken over the edges of a **non-transitive tournament is
   zero**; q-Dyson follows by summing over tournaments, only transitive ones (= permutations)
   surviving. Related: **D. Zeilberger, "A combinatorial proof of Dyson's conjecture"**,
   Discrete Math. 41 (1982) 317–321, and **I. Gessel, "Tournaments and Vandermonde's
   determinant"**, J. Graph Theory 3 (1979) (*both not accessed*).
   **Applies?** This is the closest analogy and the motivation for experiment 1: a(N) is the
   number of *transitive* balanced tournaments. But in Bressoud–Goulden the non-transitive
   terms vanish individually because of a sign/weight; here every balanced tournament has
   weight +1 and B(N) − a(N) is large (NOTES 1d, 1e). No weight was found that cancels the
   non-transitive balanced tournaments. Negative.

## Tournaments, score sequences, Eulerian orientations

5. **M. Isaev, B. D. McKay, R.-R. Zhang, "Cumulant expansion for counting Eulerian
   orientations"**, arXiv:2309.15473 (https://arxiv.org/abs/2309.15473). *Read (pp. 1–3).*
   Records: Schrijver's bounds 2^{-|E|}∏C(d_i, d_i/2) ≤ EO(G) ≤ ∏C(d_i,d_i/2)^{1/2}, the lower
   bound being Pauling's independence estimate; counting Eulerian orientations is #P-complete
   (Mihail–Winkler); McKay's EO(K_n) ~ (n/e)^{1/2}(2^{n+1}/(πn))^{(n−1)/2} for regular
   tournaments; for dense expanding graphs EO(G) ~ 2^{|E|} τ(G)^{-1/2} (2/π)^{(n−1)/2}
   exp(−¼Σ_{jk}(1/d_j+1/d_k)²) (Isaev–Isaeva), τ = number of spanning trees; the paper gives
   the full expansion in cumulants of a Gaussian on the graph Laplacian.
   **Applies?** Yes, as the right model for B(N). Our Bprod(N) = 2^{C(N,2)}∏C(2r_m,r_m)/4^{r_m}
   is exactly Pauling's estimate, and B/Bprod ∈ [0.937, 1] for N ≤ 23 is the analogue of
   their correction factor. Two differences: (a) our constraint is "in-degree from the left
   arm = in-degree from the right arm", which after a change of variables is a
   degree-constrained *subgraph* problem on the mutual graph (NOTES 1a), not an orientation
   problem, and the correlation has the opposite sign (B < Bprod, whereas EO ≥ Pauling);
   (b) the method (saddle point / cumulants of an n-dimensional integral) would give the
   asymptotics of B(N), which is not what limits us: B(N) is super-exponentially far from
   a(N). The #P-completeness is consistent with B(N) having no closed form.

6. **B. D. McKay, "The asymptotic numbers of regular tournaments, Eulerian digraphs and
   Eulerian oriented graphs"**, Combinatorica 10 (1990). *Not accessed; statement as quoted
   in source 5.* Saddle-point evaluation of CT ∏_{j<k}(x_j/x_k + x_k/x_j). Same remarks.

7. **Landau's theorem on score sequences** (H. G. Landau 1953). *Not accessed.* Characterises
   score sequences by majorisation. **Applies?** Only loosely: our D_m are differences of two
   partial scores (left-arm and right-arm in-degrees), not scores; no Landau-type criterion
   was needed since we count, not characterise.

## Mahonian and graph-inversion statistics

8. **D. Foata, D. Zeilberger, "Graphical major indices"**, J. Comput. Appl. Math. 68 (1996),
   arXiv:math/9406220 (https://arxiv.org/abs/math/9406220). *Read (pp. 1–3).*
   For a relation U on the alphabet, inv'_U(w) = Σ_{i<j} χ((x_i,x_j) ∈ U) and
   maj'_U(w) = Σ_i i·χ((x_i,x_{i+1}) ∈ U). U is *bipartitional* if there is an ordered
   partition (B_1,…,B_k) with some blocks underlined such that (x,y) ∈ U iff x's block is to
   the left of y's, or they share an underlined block (Han: (x,y),(y,z) ∈ U ⇒ (x,z) ∈ U, and
   (x,y) ∉ U, (z,y) ∈ U ⇒ (z,x) ∈ U). Theorem: inv'_U and maj'_U are equidistributed on all
   rearrangement classes iff U is bipartitional; then the generating function is a product of
   q-multinomials.
   **Applies?** Yes, as an explanation of a negative result. By the pair-sum formula (NOTES
   2a, Lean `sum_Dp`), Σ_m D_m is a graph-inversion statistic with weight 2 on the mutual
   graph and weight 1 on the one-sided graph. Neither relation is bipartitional (the window
   relation is not transitive), so no product formula is expected, and indeed
   Σ_π q^{ΣD_m} is irreducible apart from (q+1)² for 4 | N (N ≤ 12).

9. **A. Kasraoui, "A classification of Mahonian maj-inv statistics"**, Adv. Appl. Math. 42
   (2009). *Not accessed.* Classifies mixed maj/inv statistics that are Mahonian; relevant
   only as confirmation that Mahonian-ness is rare and structural.

## Sign-reversing involutions, roots-of-unity filters, Boolean analysis

10. **D. Stanton, D. White, *Constructive Combinatorics*** (Springer 1986); **A. Benjamin,
    J. Quinn, *Proofs that Really Count*** (MAA 2003). *Not accessed (standard references).*
    The technique used in NOTES 3a is of this type, with one twist: the map (move the first
    panel to the end) is a sign-reversing *bijection of order N*, not an involution.
    The closest classical relative is the cyclic-sieving / "rotation changes the statistic by
    a constant" argument.

11. **R. O'Donnell, *Analysis of Boolean Functions*** (CUP 2014; https://arxiv.org/abs/2105.10386).
    *Not accessed in this session (standard reference).* Used only for the vocabulary of
    NOTES 4: Walsh expansion, weight by degree, and the Plancherel form of
    Σ_S g(S)g(Sᶜ). The spectrum of g is not low-degree, so none of the low-degree machinery
    (hypercontractivity, junta theorems) is applicable.

## Summary

The constant-term literature offers three mechanisms for a closed form: a uniform product
over pairs (Dyson/Morris/Macdonald), a tournament sum in which non-transitive terms cancel
(Zeilberger, Bressoud–Goulden), and a bipartitional relation (Foata–Zeilberger). The fold
problem has none of the three: the pair factors depend on the window relation, the
non-transitive balanced tournaments do not cancel, and the window relation is not
bipartitional. The Eulerian-orientation literature (Pauling, Schrijver, McKay, Isaev et al.)
correctly predicts the behaviour of the *relaxation* B(N), but B(N) is too far from a(N) to
help.
