# Literature: entropy method and permanent-type bounds

**Caveat.** The session budget ran out before the sources could be re-downloaded. The
summaries below are from prior knowledge of these papers, not from a fresh reading in this
session; the bibliographic details should be checked before they are quoted elsewhere.
What is reliable is the assessment of how each technique applies to a(N), since that was
worked out here (`NOTES.txt`).

| source | what it does | applies here? |
|---|---|---|
| J. Radhakrishnan, *An entropy proof of Bregman's theorem*, J. Combin. Theory A 77 (1997) | H(σ) for a uniform perfect matching, chain rule over a random row order; the number of columns still available for row i is uniform on 1..d_i for **every** fixed σ, giving ∏ (d_i!)^{1/d_i}. | The scheme (random order + count the admissible values) is the one tested. The key property fails: the number of admissible ranks of panel m (zeros of its window bridge) depends on the sequence, between 1 and r+1, and no averaging over orders makes it sequence-independent (NOTES §2). Only the counting form survives: `sum_inv_pathProd_le` plus AM–GM, used in NOTES §3. |
| L. Brégman (1973); H. Minc's conjecture; A. Schrijver, *A short proof of Minc's conjecture* (1978); Schrijver–Valiant / Schrijver (1998) lower bounds for permanents | Upper bound ∏ (r_i!)^{1/r_i} for 0/1 permanents; lower bounds for doubly stochastic / regular matrices. | a(N) is not a permanent: validity of a cell (panel, time) depends on the rest of the permutation. No direct use. The lower-bound side (van der Waerden type) has no analogue because valid sequences can get stuck. |
| D. Galvin, *Three tutorial lectures on entropy and counting* (arXiv 1406.7872) | Chain rule, Shearer's lemma, Brégman, Kahn's independent-set bound, Dedekind. | Used as the toolbox. Shearer over coordinate sets loses about w(1−w/2N) nats per window of size w for permutations, more than the (1/2)ln(πr) a window constraint saves (NOTES §6). |
| F. Chung, R. Graham, P. Frankl, J. Shearer, *Some intersection theorems for ordered sets and graphs* (1986) | Shearer's lemma. | As above: not useful, the windows are too large and nested. |
| J. Kahn, *An entropy approach to the hard-core model on bipartite graphs* (2001); *Entropy, independent sets and antichains* (Dedekind's problem) | Conditional Shearer with carefully chosen conditioning sets. | The nested windows [1, 2m−1] make every panel's neighbourhood half the strip; no bounded-degree structure to condition on. Not applied. |
| J. Kahn, L. Lovász (unpublished); Cutler–Radcliffe, *An entropy proof of the Kahn–Lovász theorem* (2011) | Brégman for perfect matchings of general graphs via random vertex orders. | Same obstruction as Radhakrishnan. |
| N. Linial, Z. Luria, *An upper bound on the number of Steiner triple systems* (RSA 2013); *... high-dimensional permutations* (Combinatorica 2014) | Random order of revelation; each alternative is killed by a fixed number of earlier elements, so E ln N_i is computable for every fixed design. | Tested in the form "reveal t_j, alternatives killed by completed windows". Fails twice: the set of killers of an alternative value is sequence-dependent, and in a uniform order panel j completes a left window only with probability ≈ 1/j and then completes a whole clump (NOTES §2). |
| R. Glebov, Z. Luria, *On the maximum number of Latin transversals* (JCTA 2016); Z. Luria, *New bounds on the number of n-queens configurations* (2017) | Linial–Luria method for transversals and for n-queens (upper bound e^{−c n} n!). | Same mechanism; n-queens constraints are lines with bounded multiplicity, ours are half-strip windows. |
| P. Keevash, *Counting designs* / *Counting Steiner triple systems*; M. Simkin, *The number of n-queens configurations* (2021); Bowtell–Keevash, Luria–Simkin on n-queens lower bounds | Matching lower bounds by random greedy + absorption; Simkin gets the exact exponential constant by an entropy upper bound over "queenons" (limit objects) and a matching construction. | This is the right model for the conjectured second-order term N ln ln N: an upper bound through a variational problem over limit shapes. Here even the first step is missing: the path-wise budget of NOTES §5 is the only quantity for which a limit variational problem is visible. Not carried out. |
| K. F. Roth (1954), W. M. Schmidt (1972), irregularities of distribution | Lower bounds for discrepancy of N points in the square. | Already used in `experiments/upper/PROOFS.txt`; relevant background for why per-state statistics cannot give ω(N). |

## What was actually used

Only two things, both elementary: the counting form of the chain rule (a uniformly random
descent reaches a given leaf with probability 1/∏V_k) and the inequality x ≤ e^{x−1}
(weighted AM–GM) to trade a bound on ∑(f_k − V_k) for a bound on ∏V_k. The new input is
combinatorial: the kick inequality bad_{k−1} + bad_k ≥ c_k and the count of mutually visible
pairs.
