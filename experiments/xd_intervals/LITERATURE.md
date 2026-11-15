# Literature: generating trees, catalytic variables, insertion encodings

Angle: generalise a(N) to a family that satisfies a closed recurrence. What was read, what
it says, and whether it applies. Depth of reading is stated for each source.

## 1. Banderier, Bousquet-Mélou, Denise, Flajolet, Gardy, Gouyou-Beauchamps, "Generating functions for generating trees"

Discrete Math. 246 (2002) 29–55; <https://arxiv.org/abs/math/0411250>. Read: abstract,
introduction and the list of example systems (pages 1–4 of the PDF).

- A generating tree is given by an axiom `(s0)` and productions `(k) ~> (e_1(k)) … (e_k(k))`:
  a node labelled `k` has `k` children with the listed labels. Equivalently, walks on the
  integer half-line with labelled steps. With `f_{n,k}` the number of nodes of level `n` and
  label `k`, the rule is the linear recurrence `f_{n+1,k} = Σ_j π_{j,k} f_{n,j}`.
- Main results as stated in the introduction: systems with finitely many labels, or with
  labels constant except for a bounded number that depend linearly on `k`, give rational
  generating functions; "factorial" systems, where a finite modification of `{1,…,k}` is
  reachable from `k`, give algebraic ones (kernel method); systems whose coefficients grow
  too fast (radius of convergence zero) or that are too irregular give transcendental ones.
- Example: 123-avoiding permutations, where deleting the largest entry is a well-defined
  map and the number of children is a sufficient label (`(k) ~> (2)(3)…(k)(k+1)`).

Applies as a test, with a negative outcome. The method needs (a) a deletion map under which
the class is closed and (b) a label that determines the multiset of children's labels. For
semi-symmetric sequences (a) fails for every deletion tried (NOTES 5a: at N = 11 between 6%
and 37% of the sequences stay valid), and (b) fails in the strongest way: the coarsest
admissible label set has a(N)/2 elements for one-panel deletions (NOTES 5b). a(N) also grows
super-exponentially, which already puts it in the paper's "transcendental" regime.

The half-line model H(N) is the positive case: its right half is a forced "walk" and
H(2n+1) = H(n) is a one-label rule, but under halving of N+1, not under N → N+1.

## 2. Barcucci, Del Lungo, Pergola, Pinzani, "ECO: a methodology for the enumeration of combinatorial objects"

J. Difference Equations Appl. 5 (1999) 435–490, DOI 10.1080/10236199908808200. Read: only
secondary descriptions (the introduction of source 1, the abstract of source 4, and search
summaries); the paper itself was not accessible.

- ECO builds every object of size n+1 from exactly one object of size n by a local
  expansion in an "active site"; the succession rule records how the number of active sites
  changes.

Applies as the definition of what was measured: `futures.cpp` computes, for five choices of
the operator (delete N; the middle panel; {1,N}; the central pair; {N−1,N}), the minimal
number of labels of any succession rule. It is not bounded by any polynomial on the data.

## 3. West, generating trees for pattern-avoiding permutations

Discrete Math. 146 (1995) 247–262 and 157 (1996) 363–374. Not read directly; known through
source 1, which credits West with introducing generating trees for permutations with
forbidden subsequences and uses his 123-avoiding tree as Example 1.

Does not apply directly: the class of valid sequences is not closed under deletion of the
largest (or any fixed) entry, in either the position or the time reading.

## 4. Cervetti, "A generating tree with a single label for permutations avoiding the vincular pattern 1-32-4"

<https://arxiv.org/abs/2103.00246> (2021). Read: abstract only.

- Gives a one-label generating tree that explains Callan's recursive formula, which had
  only been proved through a complicated bijection.

Relevance: an example that the right insertion operator can reduce the number of labels.
That is why five different operators were tested here; none reduces the label count below
a constant fraction of a(N).

## 5. Bousquet-Mélou and Jehanne, "Polynomial equations with one catalytic variable, algebraic series and map enumeration"

J. Combin. Theory B 96 (2006) 623–672; <https://arxiv.org/abs/math/0504018>. Read: abstract
and search summary.

- A series F(u) defined by a polynomial equation with one catalytic variable u (and finitely
  many unknown series free of u) is algebraic under a mild hypothesis; the proof generalises
  the kernel and quadratic methods.

Does not apply: there is no equation to start from. A catalytic variable is a statistic for
which the refined counts satisfy a recurrence; the bisimulation count shows that no bounded
tuple of statistics works for the tested schemes. For H(N) the "catalytic" data is the wall
position, which is deterministic, so no kernel argument is needed.

## 6. Albert, Linton, Ruškuc, "The insertion encoding of permutations"

Electron. J. Combin. 12 (2005) R47; <https://doi.org/10.37236/1944>. Read: search summaries
and the description in Vatter's follow-up (arXiv 0911.2683), not the paper.

- A permutation is encoded by the sequence of insertions of its entries in increasing
  order into open slots; classes whose encodings form a regular language are characterised
  (bounded number of open slots, no long alternations), and have rational generating
  functions that can be computed by automaton.

Applies in spirit and gives a negative answer: reading a fold sequence in time order is an
insertion encoding with "slots" = unplaced panels, and experiments/fastalg already shows
that the minimal automaton has one state per live set (about 0.66·2^N). The slot count is
unbounded and the language is not regular in any useful sense.

## 7. Enumerations of specific permutation classes (survey table)

<https://en.wikipedia.org/wiki/Enumerations_of_specific_permutation_classes>. Read: the page.

- Av(1324) has no known non-recursive formula; it is enumerated by functional equations
  with many catalytic parameters (Johansson–Nakamura, Conway–Guttmann–Zinn-Justin, 50
  terms). Three two-pattern classes are conjectured not to satisfy any algebraic
  differential equation (Albert et al. 2018).

Relevance: precedent that a natural permutation family can have no single-sequence
recurrence while still being computable through a refinement with unboundedly many
parameters. The subset recursion g(S) is exactly such a refinement for a(N); the question
of this angle was whether a smaller one exists, and the measured answer is no for the
schemes tested.

## 8. Stanley, Enumerative Combinatorics 1, ch. 4 (transfer-matrix method)

Not re-read; used as background. The transfer-matrix method needs a state space of bounded
size per step. For a(N) the time-ordered state space is the live sets (fastalg), and the
panel-ordered one is the set of realisable relative orders (super-exponential). For the wall
family the state after the forced panels is trivial, which is why 2c of the notes closes.

## Summary

The literature gives a precise criterion (finite or "factorial" label sets) and a way to
measure failure (minimal label count). Applied here it gives one closed rule, for the
half-line model, and a quantitative obstruction for a(N).
