# Literature and OEIS survey (2026-11-05)

**Bottom line:** none of our sequences is in the OEIS: not the semi-symmetric counts,
their shifts, the even- or odd-indexed terms, the halved terms, the semi-minus-sym
differences, the reachable-state counts, the dead-end counts, or the first-element
triangle. Nothing in the literature studies the semi-symmetric (count-balance)
condition, and no origami source discusses the bisection-order question. The sequence
looks new and could be submitted to OEIS.

## Symmetric case = OEIS A003407 (3-AP-free permutations), θ(n)
- https://oeis.org/A003407 has a b-file to n = 200 (Heinz) and terms to n = 90 from
  Correll–Ho. Related: A296529 (by first element; row n=4 is 2,3,3,2, as for us),
  A162982, A292523, A295370.
- Davis, Entringer, Graham, Simmons, *On permutations containing no long arithmetic
  progressions*, Acta Arith. 34 (1977) 81–90.
  - θ(2n) ≥ 2θ(n)² and θ(2n+1) ≥ 2θ(n)θ(n+1), via the parity construction: the evens
    2·σ first, then the odds 2·τ−1, or the reverse.
- Sharma, EJC 16 (2009) R63.
  - θ(n) ≤ 21·θ(⌈n/2⌉)θ(⌊n/2⌋), so the growth is at most exponential.
  - At each end, at least ⌊n/2⌋−6 entries share the same parity.
- LeSaulnier & Vijay, Discrete Math. 311 (2011) 205–207. Improved lower bound.
- Correll & Ho, INTEGERS 17 (2017) #A55, arXiv:1712.00105.
  - Memoised DP on the bitset of unplaced elements, reaching n = 90.
  - Bounds of the form 2.20ⁿ ≲ θ ≲ 2.36ⁿ.
- B. S. Ho, *3AP-free permutations have no exponential growth rate*,
  arXiv:2602.13617 (2026); code at https://github.com/boonsuan/3ap-free.
  - lim θ(n)^{1/n} does not exist.
  - No closed formula is known.
- Cyclic version: orderings of Z/nZ avoiding 3-APs mod n.
  - They exist iff n is a power of 2 (Nathanson, JCTA 22 (1977)).
  - There are then exactly 2^{n−1} of them (Goh & Zhao, arXiv:2012.12339).
  - The structure is recursive parity blocks (Adenwalla, arXiv:2211.04451).

## Semi-symmetric: transferable facts
- **The parity construction still works (checked by brute force for N ≤ 11; not
  proven):** s(2n) ≥ 2·s(n)² and s(2n+1) ≥ 2·s(n)·s(n+1).
- Unlike the 3-free case, s(2k)/s(k)² is unbounded: about 21170 at k = 13. The growth
  is super-exponential: log s(n)/(n log n) rises from about 0.42 to 0.456 for n ≤ 27.

## Weaker "balance" analogues
None match the semi-symmetric condition. Near misses: A250035 (equal sums of the two
halves), A179566/7, and Kasel arXiv:2609.02939 (a dyadic balance law in a monotone-3AP
problem).

## Origami
None of these discusses bisection order:
- Demaine et al., *Folding a paper strip to minimize thickness* (arXiv:1411.6371)
  covers layer order, not crease order, and mentions "creep".
- Gjerde's precreasing guides.
- OrigamiUSA notes on grid shrinkage.
- Lang's binary-division error analysis.

## Leads
1. Count a *cyclic* semi-symmetric variant for N = 2^k, by analogy with Goh–Zhao's
   2^{n−1}.
2. Look for an Adenwalla-style parity / 2-adic decomposition, and test whether
   semi-symmetric sequences tend to start with a parity block (as in Sharma's ends
   result).
3. Algorithms: the state of the art for A003407 is memoised subset DP. Symmetry and
   meet-in-the-middle are the obvious gains.
