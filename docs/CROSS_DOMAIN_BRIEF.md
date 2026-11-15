# Cross-domain campaign: shared briefing for agents

Ten agents each attack the counting problem from a different mathematical field. This file
is the common part of every brief. Your own angle is in your prompt.

## The problem (read `README.md` and `docs/writeup/folds.tex` first, 15 minutes)

Panels `1..N`. A fold sequence is a permutation `a` of `[N]`. Step `k` places `m = a_k` on top
of the earlier set `S`. With `r = min(m-1, N-m)`, the step is **semi-symmetric** ("weakly
symmetric", "valid") iff `#{d ≤ r : m-d ∈ S} = #{d ≤ r : m+d ∈ S}`. `a(N)` counts the
sequences in which every step is valid. Goal of the whole project: **a formula for a(N),
ideally a recurrence**, or failing that any exact structure.

Equivalent forms you can use (all in Lean):
- doubling form: `P̃(2m−1) = 2P(m−1)` with `P(j) = |S ∩ [1,j]|`, extended cyclically;
- time-word form: let `t_m` = the step at which panel `m` is placed. Valid iff for every `m`,
  the number of smaller entries among the `r` positions left of `m` equals that among the
  `r` positions to the right. For `m` in the left half the window is the prefix `[1, 2m−1]`
  (nested windows); for the right half it is a suffix;
- validity of a step depends only on `(S, m)`, so `g(S) = Σ_{valid m ∈ S} g(S∖{m})`,
  `a(N) = g([N])`, and `a(N) = Σ_{|S|=k} g(S) g(Sᶜ)`;
- reversal and mirror preserve validity.

Data: `experiments/semi_counts.txt` (a(1..38)). Code you can reuse: `experiments/semi.c`,
`experiments/structure/dp.c` (generic subset DP, many modes), `rust/` (fast counter).

## Already done: do not redo (see the README tables for where)

- Recurrence searches on a(N) itself: P-recursive, C-finite, algebraic/D-algebraic GFs,
  Mahler, q-difference, Somos, Riccati, Hankel/continued fractions, 2-regular, automatic,
  OEIS transforms, 10⁶ expression trees, mod-p linear recurrences. All negative.
  (`experiments/recsearch/REPORT.txt`, `experiments/recsearch2/REPORT.txt`.)
- Prefix counts T(N,k): Ehrhart quasi-polynomials, period law, non-D-finite bivariate GF.
- Burnside mod 4 and mod 8, middle-swap involution (`Folds/Congruence*.lean`).
- Single-panel Wallis count, exact independence of compatible windows, pair correlations
  (`experiments/cluster/`), the Wallis product model.
- Parity blocks, residue-class composition, slips, neutral sets and identity (A), window
  copies and identity (B), truncated bit reversal.
- Growth bounds `(N/4096)^{N/16} ≤ a(N) ≤ N! e^{−0.0878N}`; SMC asymptotics; the
  conjecture `a(N) = N!/(κ ln N)^N`.
- Liveness of 2-prefixes (complete) and 3-prefixes (partial).
- Statistics: descents, LIS/LDS extremes, left-to-right maxima, first-panel law, descent
  polynomial tables (`experiments/arith/`, `experiments/structure2/`).
- Proof that any *time-ordered* automaton needs one state per live set
  (`experiments/fastalg/NOTES.txt`).
- Literature already surveyed: `docs/LITERATURE.md`, `docs/RECURRENCE_LITERATURE.md`.

If your angle touches one of these, read the corresponding notes first and build on them.

## What to deliver

1. **Literature.** Actually read sources from your field (WebSearch / WebFetch; papers,
   surveys, textbooks, problem collections). Write `experiments/<your dir>/LITERATURE.md`:
   each source with its URL or citation, what it says, and whether and how it applies here.
   Say so plainly when a source does not help.
2. **Experiments.** Compute before you conjecture. Check every claimed identity on all the
   data you have. Put code and outputs in `experiments/<your dir>/` and write
   `experiments/<your dir>/NOTES.txt`. Label every statement `[proven]`, `[data N ≤ …]` or
   `[conjecture]`. Record negative results too, with what exactly was tested.
3. **Lean.** Formalize every statement you prove, in `Folds/<YourFile>.lean` (Lean 4,
   Mathlib v4.35, no `sorry`, no `native_decide`; `decide +kernel` is fine for small finite
   checks). Formalize the definitions of your new objects even if the main findings are
   numerical, together with whatever exact facts about them you can prove (base cases,
   symmetries, bounds, identities). Import only core modules (`Folds.Defs`, `Folds.Basic`,
   `Folds.Recursion`, …; not the `FoldsCerts` modules). Add one `import` line to
   `Folds.lean`.
4. **Final report** (under 400 words): the findings, any candidate formula or recurrence
   with the range it was checked on, the Lean theorem names, and the negative results.
   Do not overstate: a pattern checked on 8 terms is `[data]`, not a theorem.

## Setup and rules

- `export PATH=$HOME/.elan/bin:$PATH`
- `mkdir -p .lake && ln -s /home/user/folds/.lake/packages .lake/packages && cp -a /home/user/folds/.lake/build .lake/build`
  (do not download Mathlib; `.lake` is git-ignored).
- The machine has 4 cores and 15 GB shared by ten agents. Keep every process under
  2.5 GB and use one core. Build Lean only through the semaphore:
  `flock /home/user/folds/.lake/lean-slot-$(( RANDOM % 3 )).lock lake build Folds.<YourFile>`.
  Use `run_in_background` for anything longer than a minute or two.
- Add a `.gitignore` for compiled binaries in your directory **before** compiling. Never
  commit binaries or large outputs (keep committed files under 1 MB each).
- Touch only: `Folds/<YourFile>.lean`, one import line in `Folds.lean`, and
  `experiments/<your dir>/`.
- **Commit locally only. Do NOT push.** End every commit message with:
  ```
  Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_017cuJ2S8GjCEZPVY2DthurB
  ```
- Commit early and often, so that work survives a restart.
