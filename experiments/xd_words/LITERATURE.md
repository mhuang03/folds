# Literature: combinatorics on words, the doubling map, origami

How each source was used is stated explicitly. "Fetched" means the page was read in this run;
"search summary" means only search-result abstracts were seen (paywalled or not opened);
"from memory" means a standard statement recalled without re-reading the source in this run —
treat constants quoted that way as unverified.

**Bottom line.** The counting problem (in how many orders can the N panels of a strip be
bisected so that every fold sees a balanced, or symmetric, set of earlier creases) was not
found in the origami literature, the words literature, or the OEIS. The nearest published
problems are listed in the last section. The tools of the field do apply, and gave three
exact statements (orbit formula, Toeplitz word, parking condition; see `NOTES.txt`).

## Balanced and Sturmian words

- **L. Vuillon, "Balanced words", Bull. Belg. Math. Soc. Simon Stevin 10 (2003) 787–805.**
  https://projecteuclid.org/euclid.bbms/1074791332 (search summary). Survey: a binary word is
  balanced if any two factors of equal length differ by at most one in the number of 1s;
  aperiodic balanced words are the Sturmian words (Morse–Hedlund), i.e. mechanical words
  ⌊(n+1)α+ρ⌋ − ⌊nα+ρ⌋. *Applies:* neutral sets satisfy the mechanical-word bound
  |N·P(t) − s·t| ≤ min(s, N−s) (`Neutral.hd_bounds`); `NOTES.txt` 2.3 shows they are the
  mechanical words of slope s/N that are also doubling itineraries. *Does not apply* to
  reachable or live sets: the intervals [1,k] are live, so no balance bound holds (NOTES 1.3).
- **Lothaire, *Algebraic Combinatorics on Words*, ch. 2 (Berstel–Séébold, Sturmian words).**
  (from memory.) Equivalence of balanced / mechanical / complexity n+1; Christoffel words for
  rational slopes. Used only as the dictionary for the above.
- **Fraenkel's conjecture; Tijdeman; Paquin–Vuillon, "A characterization of balanced
  episturmian sequences", Electron. J. Combin. 14 (2007) R33.**
  https://www.combinatorics.org/ojs/index.php/eljc/article/download/v14i1r33/pdf (search
  summary). Balanced words on k ≥ 3 letters with distinct frequencies are conjectured unique
  (frequencies 2^(k−i)/(2^k−1)); proved for k ≤ 7 and for episturmian words. *Relevance:*
  the Fraenkel word has the same doubling flavour (frequencies in ratio 2), and a valid
  sequence induces a k-letter word (letter = time block). I found no way to use it: prefix
  sets of valid sequences are not balanced. Negative.

## Doubling map, ordered orbits

- **S. Bullett, P. Sentenac, "Ordered orbits of the shift, square roots, and the devil's
  staircase", Math. Proc. Cambridge Philos. Soc. 115 (1994) 451–481.**
  https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/ordered-orbits-of-the-shift-square-roots-and-the-devils-staircase/FCF6897070095CB61A71F2858D76772E
  (search summary; full text paywalled.) An orbit (or closed invariant set) of t ↦ 2t on the
  circle is cyclically ordered iff it lies in a closed half-circle [μ, μ+½]; it then has a
  rotation number, is Sturmian, and μ(ν) is a devil's staircase. *Applies directly:* a neutral
  set is the finite version: by the orbit formula (`hd_cycle_neutral`) its indicator is the
  itinerary of the rotation orbit {s·m/N} with respect to [½, 1). The condition E(2c) = 2E(c)
  at *all* panel centres forces rotation number in {1/2, j/(2j+1), (j+1)/(2j+1)}. A general
  valid prefix is not an ordered orbit: its "digits" are defects outside {0,1} (NOTES 2.3).
- **Gambaudo–Lanford–Tresser; Veerman; Goldberg–Tresser on rotation-ordered orbits of
  x ↦ kx** (e.g. https://arxiv.org/pdf/1712.04506, search summary). Same circle of ideas for
  degree k; combinatorial types of periodic orbits. No counting statement that transfers.
- **Cycle structure of x ↦ 2x on Z/N** (cyclotomic cosets; standard). Used in `orbits.py`:
  number of cycles Σ_{d | odd part} φ(d)/ord_d(2). Result: no arithmetic signal in a(N)
  beyond 3 | N (NOTES 2.5).

## Paperfolding, Toeplitz words, automatic sequences

- **Allouche–Shallit, *Automatic Sequences*, ch. 5–6; Dekking–Mendès France–van der Poorten,
  "Folds!", Math. Intelligencer 4 (1982).** (from memory.) Regular paperfolding sequence
  p_n = j mod 2 for n = 2^k(2j+1); obtained by the Toeplitz pattern (0 ? 1 ?); 2-automatic.
- **J.-P. Allouche, R. Bacher, "Toeplitz sequences, paperfolding, towers of Hanoi and
  progression-free sequences of integers", Enseign. Math. 38 (1992) 315–327.**
  https://archive-ouverte.unige.ch/unige:12072 (search summary.) Toeplitz transforms generate
  paperfolding and period-doubling sequences; also links to progression-free sequences —
  noteworthy because the symmetric case here is "3-AP-free permutations".
  *Applies:* the canonical (bit-reversal) prefix sets are one-hole Toeplitz words of the
  period-doubling family, proved in Lean (`canon_prefix_word`, `tword_add_pow`); they are not
  the paperfolding sequence (NOTES 4.3).
- 2-regularity of a(N) itself was already excluded in `experiments/recsearch2`; not redone.

## Discrepancy of the van der Corput sequence

- **Béjian–Faure, "Discrépance de la suite de van der Corput", Sém. Delange–Pisot–Poitou
  (1977/78).** https://eudml.org/doc/110984 (search summary.) Exact star discrepancy;
  N·D*_N ≤ log N/(3 log 2) + 1.
- **Faure–Kritzer–Pillichshammer, "From van der Corput to modern constructions of sequences
  for quasi-Monte Carlo rules".** https://arxiv.org/pdf/1506.03764 (search summary.)
  Generalised van der Corput sequences with digit permutations have smaller discrepancy
  constants than the plain one.
- **Schmidt's lower bound** N·D*_N ≥ c·log N infinitely often (c ≈ 0.06), **best known
  constructions** ≈ 0.22·log N (from memory; constants unverified here), **Owen's nested
  scrambling**, (0,m,2)-nets and the Hammersley set (Kuipers–Niederreiter ch. 2;
  Dick–Pillichshammer) (from memory).
  *Applies:* (i) the parity-block tree family `Gen.gen` is exactly the nested base-2
  scrambling of the van der Corput order (NOTES 3.2); (ii) computed: the canonical member is
  the worst of its family and the best members reach the symmetric optimum; the best valid
  sequences match the best of all N! orderings for N ≤ 22 except N = 11, 17, 18, 19
  (NOTES 3.1); (iii) with `Upper.disc_le_of_cycDefect_le`, Schmidt's theorem already gave an
  unbounded imbalance field along every sequence; `hd_bounds_of_jm` sharpens the transfer.

## Origami

- **Fujimoto's approximation** (Fujimoto–Nishiwaki 1982; Hull, *Project Origami*, activity
  "Dividing a length into equal nths: Fujimoto approximation").
  https://cutoutfoldup.com/411-fold-a-strip-of-paper-into-approximate-n-ths.php (fetched):
  for fifths, guess 1/5, then fold the right end to the mark (→ 3/5), right end to the new
  mark (→ 4/5), left end (→ 2/5), left end (→ 1/5); "the error is reduced by a factor of two
  each time". https://kpknudson.com/blog/2013/2/26/binary-fractions (search summary): the
  left/right sequence is the binary expansion of 1/n (attributed there to Hull's book).
  *Relation:* each Fujimoto fold is exactly this project's step — fold the nearer edge onto a
  reference crease, creating the crease halfway — and the marks follow one orbit of the
  halving map on Z/n (the inverse of `phi`). The literature treats one orbit and its error
  contraction. It does not ask in which orders all N panels can be bisected, and has no
  balance condition.
- **R. Lang, "Origami and Geometric Constructions" (binary folding algorithm).** (from
  memory; the search found only passing mentions.) A fraction with denominator 2^k is located
  by reading its binary digits from the last one, folding the top or bottom edge to the
  previous crease. Same map, again a single path in the tree of `phi_iter_pow_two`.
- **Stamp folding / map folding: OEIS A000136** https://oeis.org/A000136 (fetched): number of
  ways of folding a strip of n labelled stamps, 1, 2, 6, 16, 50, 144, 462, 1392, 4536, 14060,
  46310, 146376; Koehler, J. Combin. Theory 5 (1968) 135–152; Lunnon, Math. Comp. 22 (1968)
  193–199; a(n) = n·A000682(n) (semi-meanders); no recurrence given. *Nearest folding count,
  but a different object:* it counts final layer orders (exponential growth), whereas a(N)
  counts time orders of creasing (super-exponential growth). No transfer found.
- **Di Francesco–Golinelli–Guitter, "Meander, folding and arch statistics",
  arXiv:hep-th/9506030** (search summary): meanders via recursion, matrix models, exact
  solutions only for simpler relatives; the enumeration itself is open and studied by
  extrapolation (n ≤ 29 in a later paper). Parallel in status (no formula, numerics only),
  not in structure.
- **Folding complexity of pleats.** Ito–Kiyomi–Imahori–Uehara, "Complexity of pleat folding"
  (https://erikdemaine.org/papers/PleatFolding_JCCGG2009/paper.pdf, search summary);
  Demaine et al., "Folding a paper strip to minimize thickness" (arXiv:1411.6371, already in
  `docs/LITERATURE.md`): the minimum number of simple folds for a mountain–valley pattern is
  polylogarithmic for pleats. This is about the *number* of folds when layers are folded
  together, not about orders of single bisections.
- **Hull, counting flat foldings of crease patterns** (search summary of
  https://joeslote.com/documents/origami_undergrad_thesis.pdf and Hull's survey): counts
  mountain–valley assignments and layer orders, not fold orders.
- Searches for "order of folds", "bisect each panel", "pleat precreasing order" and
  "number of ways" returned nothing on bisection orders; `docs/LITERATURE.md` reached the
  same conclusion earlier (Gjerde's precreasing guides, grid shrinkage notes).

## Not consulted
Kuipers–Niederreiter, Lothaire, Allouche–Shallit, Lang and Hull's books were not available
online in this run; statements attributed to them are from memory. Tanton's "folding
fractions" and Hull's *Origametry* were not found by the searches made.
