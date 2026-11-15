# Literature for the connection-matrix / tensor-rank angle

How each source was used is stated honestly: "read" means the text itself was read in this
session; "abstract / secondary" means only the abstract or statements of the result in
other papers were consulted; "from memory" means a standard textbook fact that was not
re-read here.

## Graph limits: connection matrices

1. **M. Freedman, L. Lovász, A. Schrijver, "Reflection positivity, rank connectivity, and
   homomorphism of graphs"**, J. Amer. Math. Soc. 20 (2007); arXiv:math/0404468.
   https://arxiv.org/abs/math/0404468 (read: sections 1-3).
   For a graph parameter f and k-labelled graphs G1, G2 (glued along the labels), the
   connection matrix is M(f,k)[G1,G2] = f(G1 G2). Theorem 2.3: homomorphism numbers into a
   weighted graph H are reflection positive (all M(f,k) positive semidefinite) with
   rank M(f,k) <= |V(H)|^k. Theorem 2.4: the converse. Example 3.1 (perfect matchings: rank
   2^k but not positive semidefinite) shows the two conditions are independent.
   *Applies as a template.* Our M_{X,Y}[sigma,tau] is the connection matrix for gluing two
   ordered half-strips. Both FLS conditions were tested and both fail: the rank is
   factorial (NOTES sections 1-3), and the mirror-reflected form has about as many negative
   as positive eigenvalues and zero diagonal (NOTES section 5). So a(N) is not a partition
   function of a vertex model across any of the cuts examined.
2. **L. Lovász, "Large networks and graph limits"**, AMS Colloquium Publ. 60 (2012),
   ch. 4 ("Graph parameters and connection matrices": 4.2 connection matrices, 4.3 finite
   connection rank) and ch. 5-6. https://bookstore.ams.org/COLL/60 (table of contents
   consulted; content from memory). Finite connection rank is the hypothesis under which a
   parameter is computable in polynomial time on bounded-treewidth graphs. *Applies as the
   "rank gives an algorithm" principle;* here the ranks are not finite or small, so the
   principle gives nothing.

## Rational series and weighted automata

3. **M. Fliess, "Matrices de Hankel"**, J. Math. Pures Appl. 53 (1974); **J. W. Carlyle,
   A. Paz** (1971); **J. Berstel, C. Reutenauer, "Noncommutative rational series with
   applications"**, Cambridge UP 2011 (ch. 2). (Secondary: the theorem as restated in
   Kiefer et al., "On the complexity of equivalence and minimisation for Q-weighted
   automata", arXiv:1302.2818, and in Balle-Mohri's work on Hankel matrices; books not
   re-read.) A series over a field is recognisable iff its Hankel matrix has finite rank,
   and the rank is the minimal number of states.
   *Applies directly.* It is the reason why rank M is a lower bound for any linear transfer
   scheme. fastalg section 1 used it for the time cut (rank = #live sets); here it is used
   for words in the insertion-position alphabet (spatial cut) and for the parity cut.

## Tensor networks

4. **U. Schollwöck, "The density-matrix renormalization group in the age of matrix
   product states"**, Ann. Phys. 326 (2011); arXiv:1008.3477.
   https://arxiv.org/abs/1008.3477 (abstract; content from memory).
5. **R. Orús, "A practical introduction to tensor networks: matrix product states and
   projected entangled pair states"**, Ann. Phys. 349 (2014); arXiv:1306.2164.
   https://arxiv.org/abs/1306.2164 (abstract; content from memory).
   The minimal bond dimension of a matrix product state across a cut is the Schmidt rank
   of the coefficient tensor reshaped as a matrix across that cut.
   *Applies as a dictionary.* The indicator of valid sequences, written in the Lehmer /
   insertion code of the time word (site j = time rank of panel j among panels 1..j), is a
   tensor whose bond dimension across site j is rank M_{[1,j],[j+1,N]}: the profile
   1, 2, 4, 14, 32, 156, 572, 156, ... of NOTES section 2. The time-ordered MPS has bond
   dimension #live sets. Neither obeys an area law; the spatial one is smaller only for
   N <= ~20.

## Communication complexity

6. **E. Kushilevitz, N. Nisan, "Communication complexity"**, Cambridge UP 1997, ch. 1-2
   (from memory), and the log-rank conjecture page
   https://en.wikipedia.org/wiki/Log-rank_conjecture (read): D(f) >= log2 rank(M_f);
   fooling sets; best upper bound O(sqrt(rank)) (Lovett; Sudakov-Tomon).
   *Applies partly.* The rank lower-bound principle is the same as 3. The fooling-set
   method is what proves rank = #live sets for the time cut (disjoint supports). For the
   spatial and parity cuts no fooling set / triangular family was found, so the
   superexponential rank is [data], not a theorem. The pair of middle panels (k, k+1)
   gives a "greater-than" sub-structure (used in the trace proof of NOTES section 5), which
   only yields rank >= k.

## Permutation classes

7. **V. Vatter, "Permutation classes"**, in Handbook of Enumerative Combinatorics (2015);
   arXiv:1409.5159. https://arxiv.org/abs/1409.5159 (read: sections 1-2 in part; the
   structural sections from memory).
8. **M. H. Albert, S. Linton, N. Ruškuc, "The insertion encoding of permutations"**,
   Electron. J. Combin. 12 (2005) R47.
   https://www.combinatorics.org/ojs/index.php/eljc/article/view/v12i1r47 (abstract).
   Classes whose insertion encoding is regular (boundedly many open slots) have rational
   generating functions; finitely labelled generating trees are a special case.
9. **M. H. Albert, M. D. Atkinson, "Simple permutations and pattern restricted
   permutations"**, Discrete Math. 300 (2005) (abstract / secondary). Finitely many simple
   permutations imply an algebraic generating function, via the substitution decomposition.
   *Do not apply.* The valid time words are not a permutation class (not closed under
   deleting entries: the windows change), they grow like N!/(log N)^N, far above the
   Marcus-Tardos exponential bound for proper classes, and the insertion-encoding state
   count is exactly the spatial-cut row-class count of NOTES section 2, which is
   superexponential. The substitution decomposition is irrelevant here: intervals of
   panels are not preserved by the doubling windows. (The composition theorem a(qn) >=
   a(q) a(n)^q is an inflation by residue classes, not by intervals.)

## Project-internal

10. `experiments/fastalg/NOTES.txt` sections 1, 3 (time cut; spatial and parity cuts at
    N = 10, 12), `experiments/symratio/PROOFS.txt` and `Folds/SymRatio.lean` (bounded
    parity-cut rank in the 3-AP-free case), `Folds/Neutral.lean` (the sets E_d).
