# Literature: partial commutation, heaps, weak order

**Caveat.** Because of a tight session budget none of these sources was re-fetched from the
network in this session; the summaries are from memory of the standard statements, and every
statement that is *used* in `NOTES.txt` was either re-proved there or checked by computation
(noted below). URLs are the usual locations and were not re-verified. No OEIS lookup of
`K(N)`, `AO(N)` or the signed counts was done; that remains to do.

## Trace monoids and heaps

1. **P. Cartier, D. Foata, *Problèmes combinatoires de commutation et réarrangements*,
   Lecture Notes in Math. 85, Springer 1969** (electronic reedition:
   https://www.mat.univie.ac.at/~slc/books/cartfoa.html).
   Free partially commutative monoid; normal form as a sequence of commuting cliques; the
   inversion formula `Σ traces = 1 / Σ_{cliques C} (−1)^{|C|} C`.
   *Applies, partly.* The swap relation on valid sequences turned out to be a **fixed**
   independence relation `I_N` (NOTES §1), so `V_N` is a union of multilinear traces. The
   inversion formula counts all multilinear traces: `AO(N) = Σ_k (−1)^k r_k (N−k)!`
   (NOTES §4, verified against a subset DP for N ≤ 22). It does not count the valid ones,
   because validity is not a product of local weights. The inclusion–exclusion over maximal
   pieces does carry over and gives the recursion for `K(S)` (NOTES §2d).

2. **G. X. Viennot, *Heaps of pieces I: basic definitions and combinatorial lemmas*, LNM 1234
   (1986) 321–350**; **C. Krattenthaler, *The theory of heaps and the Cartier–Foata monoid***
   (appendix to the reedition of [1], https://www.mat.univie.ac.at/~kratt/artikel/heaps.pdf).
   Heaps = traces as posets; inversion lemma `heaps = 1/trivial heaps (signed)`, the
   "heaps with maximal pieces in M" lemma, logarithmic lemma for pyramids.
   *Applies as a language.* A valid trace is a heap over two columns (L and R); its linear
   extensions are lattice paths. The "maximal pieces" lemma is what gives the `K` recursion.
   The pyramid/logarithmic lemma has no use here (each piece occurs once; no generating
   function in which heaps concatenate freely).

3. **V. Diekert, G. Rozenberg (eds.), *The Book of Traces*, World Scientific 1995**
   (chapters on semi-commutations and on context-dependent / "conditional" commutation).
   *Does not apply in the way the brief expected*: context-dependent commutation is not
   needed, since the commutation here is context-free once both orders are restricted to
   valid sequences. The relevant notion is rather a trace-closed language (`V_N` is closed
   under the trace congruence); it is not recognised by a small automaton
   (`experiments/fastalg`).

4. **I. Gessel, *Acyclic orientations and chromatic generating functions*, Discrete Math. 232
   (2001)**, and R. Stanley, *Acyclic orientations of graphs*, Discrete Math. 5 (1973).
   Multilinear traces ↔ acyclic orientations of the dependence graph, counted by `|χ(−1)|`.
   *Applies*: `D_N` is chordal, so `AO(N) = B! · Π (B − b_(i) + i)` (NOTES §4; checked N ≤ 30
   against the rook formula).

5. **J. Goldman, J. Joichi, D. White, *Rook theory I: rook equivalence of Ferrers boards*,
   Proc. AMS 52 (1975)**. Factorisation of the rook polynomial of a Ferrers board.
   *Applies*: `I_N` is a Ferrers board, which explains the smooth factorisations of `AO(N)`.
   Only a statement about the context-free count.

## Weak order, linear extensions, congruences

6. **A. Björner, M. Wachs, *Permutation statistics and linear extensions of posets*, JCTA 58
   (1991) 85–114.** The linear extensions of a naturally labelled poset form a convex subset
   of the weak order; an interval exactly for certain two-dimensional ("regular") labellings.
   *Applies*: each swap class is the set of linear extensions of a heap of width 2 whose two
   chains are L < R, hence an interval (re-proved directly; brute-force check N ≤ 8). The new
   fact, not in this paper, is that the *union* `V_N` is convex (Lean
   `semiSymmetric_of_weak_between`).

7. **N. Reading, *Lattice congruences of the weak order*, Order 21 (2004)**; *Cambrian
   lattices*, Adv. Math. 205 (2006); *Noncrossing arc diagrams and canonical join
   representations*, SIAM J. Discrete Math. 29 (2015). Congruences of the weak order on
   `S_n` are determined by sets of contracted join-irreducibles (arcs) closed under forcing;
   polygon forcing rule.
   *Applies*: `I_N` is an upper set of pairs, so "contract every cover that exchanges an
   independent pair" is forcing-closed: the trace equivalence is a lattice congruence `Θ_N`
   (forcing closure verified by computer for N ≤ 6, `weak.py`). `V_N` is a union of classes
   and an antichain of the quotient. `Θ_N` is not a Cambrian congruence (its quotient has
   `AO(N)` elements, not Catalan many). This describes where `V_N` sits; it does not count it.

8. **J. Stembridge, *On the fully commutative elements of Coxeter groups*, J. Algebraic
   Combin. 5 (1996).** Elements whose reduced words form one commutation class; heaps of
   fully commutative elements. *Does not apply*: our words are permutations of panels under a
   non-Coxeter commutation relation; only the heap picture is shared.

9. **G. Kreweras, *Sur une classe de problèmes de dénombrement liés au treillis des partitions
   des entiers*, Cahiers du BURO 6 (1965)**; Lindström–Gessel–Viennot. Number of chains /
   shapes between two partitions as a determinant. *Applies*: size of a swap class = number
   of lattice paths between two boundaries (`classes.c` uses the equivalent DP). Gives each
   term of `a(N) = Σ e(class)` but not the sum.

## Homotopy of chains

10. **E. Babson, H. Barcelo, M. de Longueville, R. Laubenbacher, *Homotopy theory of graphs*,
    J. Algebraic Combin. 24 (2006)**; Barcelo–Laubenbacher, *Perspectives on A-homotopy
    theory*, Discrete Math. 298 (2005). Discrete (A-)homotopy; maximal chains up to diamond
    moves. *Applies only as a reformulation*: valid sequences are maximal chains of the
    poset of reachable sets, a valid swap is a diamond move, so `K(N)` is the number of
    diamond-homotopy classes of maximal chains. Since every class is a distributive lattice
    (contractible), there is no higher invariant to extract.

## Negative summary

None of these theories yields a formula for `a(N)` or `K(N)`. The exact products exist only
for the unconstrained trace count `AO(N)`.
