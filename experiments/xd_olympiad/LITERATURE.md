# Literature: the competition-mathematics toolkit

Status flags: **[fetched]** = page read in this session (WebSearch/WebFetch);
**[memory]** = standard source cited from memory, statement not re-checked online in this
session (the network budget went to the sources that mattered for the findings).
"Applies" refers to the semi-symmetric count a(N); see `NOTES.txt` for what each technique gave.

## 1. The source problem and its relatives

| source | what it says | applies? |
|---|---|---|
| All-Union Mathematical Olympiad 1974 (grades 9-10), A. I. Plotkin; Kvant problem M271, <https://brain-kvant.pages.dev/271/> **[fetched]** | Arrange 1..n so that the arithmetic mean of two numbers never stands between them. Solution: odds first, then evens, each block built recursively by x -> 2x-1, x -> 2x; reduce to n a power of 2. | This is the symmetric (3-AP-free) case, A003407. The odds/evens recursion is `Folds/Blocks.lean`, `Counting.lean` (a(2n) >= 2a(n)^2). In the semi case the parity blocks are only 0.16% of a(20), so the olympiad recursion gives a lower bound, not the count. |
| Discussions of the same problem: <https://www.physicsforums.com/threads/arranging-1-to-n-so-no-average-appears-between-two-numbers.563787/>, <https://www.cut-the-knot.org/htdocs/dcforum/DCForumID6/693.shtml>, LeetCode 932 "Beautiful Array" **[fetched: search summaries]** | Same construction; "it suffices to treat n = 2^k". | Same as above; nothing about counting. |
| ISL 2008 C2 **[memory]** | Count permutations of {1..n} with k dividing 2(a_1+..+a_k) for all k; answer 3*2^(n-2). Method: look at the LAST element (it is 1, n or forced), delete it, recurse. | Model for attempt 1 (recursion on a distinguished element). Here deleting panel 1 changes the two end points of every left window (NOTES 3.1): the deletion is valid only under a betweenness condition, and the lift count has no closed form. Obstruction. |
| IMO 1989/6 **[memory]** | Permutations of {1..2n} with some \|x_i - x_{i+1}\| = n outnumber the others. Method: an injection/involution exchanging two entries. | Model for attempt 5. Exchanging the times of two panels is never a symmetry of V_N (NOTES 7.1); the working involutions are mirror, reversal and commuting swaps. |
| IMO 1987/1 **[memory]** | sum_k k p_n(k) = n! (fixed points), by double counting pairs (permutation, fixed point). | Model for attempt 3: pairs (valid sequence, valid alternative move), NOTES 5. Gives M(1) = (N/2) a(N) (even N) and the availability-time identity, nothing closed in general. |
| IMO Shortlist combinatorics 2001-2023, searched by topic ("permutation", "between", "arithmetic mean", "balanced") **[fetched: search only]** | The search surfaced ISL 2021 C5 (circle of 2n+1 students, k neighbours on each side) and ISL 2005 C7 (two permutations with n \| a_i - b_i - c_i); neither concerns balance of earlier elements in a window. | No shortlist problem with a local balance condition of our type was found. Not applicable. |
| Putnam, Miklós Schweitzer, Tournament of Towns **[memory, not searched in depth]** | Typical counting tools: ballot numbers (Putnam-style lattice path problems), sign-reversing involutions, generating functions. | Only as a toolbox; no problem with our window rule is known to me. |

## 2. Textbooks and handouts (techniques)

| source | technique | outcome here |
|---|---|---|
| A. Engel, *Problem-Solving Strategies* (Springer 1998), ch. 1 (invariance principle), ch. 3 (extremal principle), ch. 5 (enumerative combinatorics) **[memory]** | Invariants mod 2, monovariants, "take the extreme element", recursion and bijection. | Invariants: exhaustive search for linear invariants of the time vector (NOTES 6): only sum t_m and "middle panel at an odd step". Extremal: panels 1 and N (radius 0) and the middle panel were used as distinguished elements (NOTES 3). |
| Yufei Zhao, olympiad handouts, <https://yufeizhao.com/olympiad/> ("Bijections", "Counting in two ways" MOP 2007, "Combinatorics: counting in two ways, generating functions, algebraic combinatorics" AwesomeMath 2007) **[fetched: index page via search]** | Bijections, double counting, sign-reversing involutions, linear-algebra method. | Double counting of windows containing a panel (NOTES 5.1); sign-reversing involutions (NOTES 2). |
| Evan Chen, *The Napkin* and OTIS/EGMO-style handouts, <https://web.evanchen.cc/> **[memory]** | Generating functions, linearity of expectation, "global" counting. | Expected number of valid moves along a random valid sequence (NOTES 5.2): data only. |
| Pranav A. Sriram, *Olympiad Combinatorics* (online notes), ch. on counting in two ways, processes, invariants **[memory]** | Processes and potential functions. | The Path Lemma potential is already in `experiments/pathlemma`; no new potential found. |
| M. Bóna, *A Walk Through Combinatorics*; Benjamin & Quinn, *Proofs that Really Count*; Andreescu & Feng, *A Path to Combinatorics for Undergraduates* **[memory]** | Reflection principle, ballot theorem, Catalan bijections, signed involutions ("description-involution-exception"), inclusion-exclusion. | Bridge form of the Wallis count (NOTES 4.1); inclusion-exclusion over commuting cliques gives the class recursion (NOTES 1.4). |

## 3. Ballot theorem, cycle lemma, reflection

| source | what it says | applies? |
|---|---|---|
| Bertrand's ballot theorem / Dvoretzky-Motzkin cycle lemma, <https://en.wikipedia.org/wiki/Bertrand%27s_ballot_theorem> **[fetched: search summary]**; Raney's lemma as quoted in "The bricklayer problem and the Strong Cycle Lemma", <https://arxiv.org/abs/math/9802026> **[fetched: search summary]** | Among the cyclic shifts of a sequence with sum +1 exactly one has all partial sums positive. | The single-panel condition is "insert m at a zero of a bridge", an expected-number-of-zeros statement (sum_k C(2k,k)C(2r-2k,r-k) = 4^r), not a positivity condition, so the cycle lemma does not apply; the count is the Wallis factor (already `Folds/Wallis.lean`). For joint conditions the bridges share one permutation; see NOTES 4. |
| Kreweras / Steck determinants for paths between two boundaries (Mohanty, *Lattice Path Counting and Applications*, 1979) **[memory]** | Number of monotone paths with the i-th vertical crossing in a prescribed interval is a determinant of binomials. | For a FIXED pair (sigma, rho) the left-half-only relaxation is exactly of this type (NOTES 1.2, 4.2); the sum over (sigma, rho) is the obstruction. |

## 4. Signs of linear extensions, partial commutation (found to be the relevant theory)

| source | what it says | applies? |
|---|---|---|
| R. P. Stanley, "Some remarks on sign-balanced and maj-balanced posets", Adv. Appl. Math. 34 (2005), <https://arxiv.org/abs/math/0211113>, read via <https://ar5iv.labs.arxiv.org/html/math/0211113> **[fetched]** | A poset is sign-balanced if half of its linear extensions are even. Thm 1.1 (Ruskey): if every non-minimal element is above at least two minimal elements, swap the first two entries. Lemma 2.1 / Cor. 2.2: promotion is parity-reversing iff every maximal chain length l has n = l (mod 2). Thm 3.5 (White): imbalance of an m x n rectangle is 0 if m = n (mod 2), m, n > 1, else a number of shifted tableaux. Prop. 3.7: recursion of the inversion polynomial over corners. | Directly applicable: V_N is a union of sets of linear extensions of width-2 posets (NOTES 1), and D(N) is the total imbalance. Ruskey's swap is the block involution of NOTES 2.4. Stanley's corner recursion is the signed subset DP used in `xd.c`. Promotion does not act on V_N (it changes the poset). The paper has nothing on width-2 posets specifically. |
| D. Soukup, "Complexity of sign imbalance, parity of linear extensions, and height 2 posets", <https://arxiv.org/abs/2311.02203> **[fetched: search summary]** | Sign imbalance is #P-hard in general. | Explains why no formula for D(N) should be expected from the poset alone; our posets have width 2, where each class imbalance is a q = -1 path count. |
| P. Cartier, D. Foata, *Problèmes combinatoires de commutation et réarrangements* (LNM 85, 1969), <https://www.mat.univie.ac.at/~slc/books/cartfoa.html>; C. Krattenthaler, "The theory of heaps and the Cartier-Foata monoid", <https://www.mat.univie.ac.at/~kratt/artikel/heaps.pdf>; X. Viennot, heaps of pieces **[fetched: search summaries]** | Partially commutative monoids; Möbius inversion: sum over commuting cliques C of (-1)^{\|C\|} = inverse of the generating function of traces. | Applied in NOTES 1.4: the classes of valid sequences are counted by inclusion-exclusion over commuting cliques (size <= 2), giving tau(1..26). |

## 5. What did not help

* Cycle lemma / reflection: no positivity condition in the problem (section 3).
* Olympiad recursions on a distinguished element (ISL 2008 C2 type): the deletion criterion
  is exact but not closed (NOTES 3).
* Generating-function tricks (snake oil, exponential formula, Lambert series): identity (A)
  is not a convolution of one sequence (NOTES 8.2).
* LTE / p-adic tricks: a(N) has no product structure to lift (NOTES 8.1).
