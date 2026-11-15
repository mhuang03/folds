# Literature for the weak-order / reciprocity angle

Status of each source: **read** (text fetched and the quoted statements checked), **abstract**
(only the abstract or a search summary was seen), **cited** (standard reference, not opened in
this session). Results are in `NOTES.txt`.

## Read

**M. Beck, R. Sanyal, *Combinatorial Reciprocity Theorems*, AMS GSM 195 (2018).**
https://matthbeck.github.io/papers/crt.pdf (read: §1.1, §1.3, §2.1–2.3).
- Thm 1.1.5 (Stanley): `(-1)^d χ_G(-n)` = number of compatible pairs (acyclic orientation,
  n-colouring); `(-1)^d χ_G(-1)` = number of acyclic orientations.
- Thm 1.3.2: `(-1)^|Π| Ω°_Π(-n) = Ω_Π(n)` (strict vs weak order polynomial).
- Cor 1.3.4: `χ_G(n) = Σ_ρ Ω°_{Π(ρG)}(n)` over acyclic orientations ρ.
- Prop 2.1.5, eq. (2.3.2): the zeta polynomial `Z_Π(n) = ζ^n(0̂,1̂)`, and
  `Z_Π(-n) = μ^n(0̂,1̂) = Σ μ(x_0,x_1)⋯μ(x_{n-1},x_n)` over multichains.
- Thm 2.3.2 (distributive lattices) and Thm 2.3.3 (Eulerian posets: `Z(-n) = (-1)^r Z(n)`).

*Applies directly.* Convention (c): validity depends only on the acyclic orientation of the
visibility graph `G_N` induced by the sequence, so `A^c_N(q)` is the sum of `Ω°` over the
*balanced* acyclic orientations (Cor 1.3.4 restricted), and Thm 1.3.2 gives the exact reciprocity
`(-1)^N A^c_N(-q) = Σ_O Ω(P_O, q)`; at `q = 1` the number of balanced acyclic orientations
(NOTES §4). Convention (d): `A^d_N` is the zeta polynomial of the fold poset, so
`A^d_N(-1) = μ(0̂,1̂)` and (2.3.2) gives `A^d_N(-2)` (NOTES §5). The book itself warns (after
(2.3.1)) that zeta polynomials at negative integers have no counting interpretation in general;
our fold poset is an instance: it is neither distributive nor Eulerian, and `μ` is erratic.

**OEIS** (https://oeis.org, JSON search; 80 sequences, `oeis_out.txt`). A003407 (3-AP-free
permutations) is the symmetric top column. Only trivial hits otherwise: A002620 (quarter squares)
for the number of symmetric copies, A014616 for the symmetric column `k = 2`. None of the
semi-symmetric columns, diagonals, Euler characteristics, `ao(N)` or `μ` values is in the OEIS.

## Abstract / search summary only

**H.-J. Bandelt, V. Chepoi, K. Knauer, *COMs: complexes of oriented matroids*, JCTA 156 (2018).**
https://arxiv.org/abs/1507.06111. Realisable COMs are hyperplane arrangements restricted to an
open convex set; linear extensions of a poset (the braid arrangement restricted to an order cone)
are a main example. *Relevance:* each component of the (c)-complex `K_N` is exactly such an
object. The abstract does not state contractibility; the body is said (search summary) to treat
it. We therefore prove only what we need (Euler characteristic 1 per component, from Thm 1.3.2
above) and leave contractibility as a conjecture.

**P. Cartier, D. Foata, *Problèmes combinatoires de commutation et réarrangements* (1969);
C. Krattenthaler, *The theory of heaps and the Cartier–Foata monoid*.**
https://www.mat.univie.ac.at/~kratt/artikel/heaps.pdf. Commutation classes of words = heaps =
linear extensions of a poset. *Relevance:* the components of the flip graph of valid fold
sequences are commutation classes for the independence relation "mutually invisible panels"
(NOTES §4). Only the standard correspondence is used.

**R. Stanley, *Acyclic orientations of graphs*, Discrete Math. 5 (1973).** Via Beck–Sanyal
Thm 1.1.5 and a survey (arXiv:2007.05217). Same content as above.

**B.-H. Hwang et al., *Acyclic orientation polynomials and the sink theorem for chromatic
symmetric functions*** (arXiv:1910.10920). Refines acyclic-orientation counts by sinks.
*Not used:* a sink-refined version of `ao(N)` was not computed.

## Cited (not opened in this session)

- R. Stanley, *Combinatorial reciprocity theorems*, Adv. Math. 14 (1974); *Ordered structures and
  partitions*, Mem. AMS 119 (1972); EC1 §3.12 (zeta polynomial), §3.15 (P-partitions).
- M. Beck, T. Zaslavsky, *Inside-out polytopes*, Adv. Math. 205 (2006). `A^c_N(q)` is an
  inside-out count for the cube and the graphic arrangement of `G_N`, restricted to the regions of
  balanced orientations; the restriction is not given by a subarrangement, so the theory gives the
  reciprocity (already obtained from order polynomials) and nothing more.
- A. Björner, M. Wachs, *Shellable nonpure complexes and posets*; A. Björner, P. Edelman,
  G. Ziegler, *Hyperplane arrangements with a lattice of regions* (1990). Would apply if the
  (d)-complex were shellable or the fold poset a lattice. *Does not apply:* the h-vector of the
  (d)-complex has negative entries from `N = 3` on (`analysis_out.txt`), so the complex is not
  shellable (not even Cohen–Macaulay).
- R. Forman, *Morse theory for cell complexes* (1998); D. Kozlov, *Combinatorial Algebraic
  Topology* (2008). The flip lemma (`euler_flip`) is an acyclic matching in this sense (match a
  weak order with the one where panel `x` is split off its block); it is complete for even `N` in
  convention (a) and leaves the chains starting `{1},{N},{c}` critical for odd `N`.
- J. Davis, R. Entringer, R. Graham, G. Simmons, *On permutations containing no long arithmetic
  progressions*, Acta Arith. 34 (1977); the repository's `docs/LITERATURE.md` for A003407.
  The parity recursion of 3-AP-free permutations is what produces the doubling recursions of the
  symmetric Euler characteristics (NOTES §6); none of them survives in the semi-symmetric case.

## What did not help

Fubini numbers / ordered Bell polynomials: the unrestricted count of weak orders; the valid
counts are not a simple thinning of them (no fit tried beyond OEIS lookups). Reciprocity for
convention (a): `(-1)^N A_N(-q)` changes sign irregularly. For convention (b) it is positive on all
data (`N ≤ 22`, `q = 1, 2, 3`), but no interpretation was found.
