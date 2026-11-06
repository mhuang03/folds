# `folds`: fast counting of semi-symmetric fold sequences

The problem statement and the reformulations are in the top-level `README.md`. In
this crate, panels are 0-indexed bits `p = m-1` of a `u64` mask. `g(S)` is the number
of valid orderings that build the set `S`.

```
cargo run --release -- semi 1 33              # prints "N a(N) time" for N = 1..33
cargo run --release -- sym 1 24               # symmetric variant (OEIS A003407)
cargo run --release -- semi 34 --mod32 4      # u32 residues, 4 moduli + CRT (half memory)
cargo run --release -- semi 35 --mod16 7      # u16 residues (quarter memory)
cargo run --release -- semi 34 --blocks -v     # block-streamed layers (see below), u64
cargo run --release -- residue semi 36 8 3 --blocks   # one u8 residue (index 3 in the moduli table)
cargo run --release -- crt 8 r0 r1 ... r12     # CRT of u8 residues (checks the redundant one)
cargo run --release -- peak 36 37              # simulated peak memory of --blocks and --sub
FOLDS_SPILL=/scratch/dir folds residue semi 37 8 0 --blocks   # layers >= 1 GB file-backed
FOLDS_SPILL=/scratch/dir FOLDS_ANON=3.5 folds residue semi 38 8 0 --sub 4 -v   # sub-blocks (below)
results/run_sub.sh 38 results/n38_u8.log 0 1 2      # chain of --sub residue runs, with logs
cargo run --release -- stats semi 26          # refined statistics (see below)
cargo run --release -- check                  # validation (brute force + known terms)
cargo test --release                          # unit tests (rule & indexing bijection)
```
`--threads T` sets the worker count (default 3). `-v` prints progress for each layer.
The release profile uses fat LTO, `codegen-units=1`, and `target-cpu=native`
(`.cargo/config.toml`).

New terms are recorded in `results/semi.txt`.

## Algorithm

1. **Meet in the middle (reversal).** `f(S) = g(S^c)`, so
   * even `N = 2k`: `a(N) = Σ_{|S|=k} g(S)·g(S^c)`
   * odd `N = 2k+1`: `a(N) = Σ_{|S|=k} g(S) · Σ_{p∉S, (S,p) valid} g((S∪p)^c)`,
     where `(S∪p)^c` again has size `k`.

   So only layers `0..⌊N/2⌋` are computed, and only two of them are held in memory at
   a time. For odd `N`, the default is the **fused** form
   `a = Σ_{|U|=k+1} g(U)·g(U^c)` (`U^c` lies in layer `k`). Layer `k+1` is computed
   row by row into a scratch buffer and consumed at once, so it is never stored. This
   needs 1 random lookup per entry instead of ~k/2. For N=35 the unfused combination
   took > 20 min per residue under load, and the fused one takes a few minutes. The
   direct formula is kept as `count_direct` and is cross-checked in `folds check`.
2. **Pull DP, layer by layer:** `g(T) = Σ_{p∈T, (T\p,p) valid} g(T\p)`. Each entry is
   written exactly once, so rows are processed in parallel with rayon and no atomics.
   Validity is two popcounts (`semi`) or one bit-reversal compare (`sym`).
3. **Mirror-orbit dense indexing (`layout.rs`).** Split `S = (L, c, R)`: `L` is the left
   half, `c` is the middle panel when `N` is odd, and `R` is the right half *bit-reversed*.
   The mirror then just swaps `L ↔ R`. Orbits are stored in blocks `(i=|L|, j=|R|, c)`
   with `i ≤ j`. An off-diagonal block is a full `C(h,i)×C(h,j)` matrix with
   row = colex-rank(L). A diagonal block is a triangle. `index(S)` is O(1) using two
   `2^h`-entry tables (rank and bit-reversal, `h = ⌊N/2⌋`). A layer takes
   `≈ C(N,k)/2` words with no hashing and no key storage. This matters because the sets
   are *not* sparse: 70–85% of the `k`-sets near the middle are reachable, and ≈ 67%
   are "alive" (both `g(S)` and `f(S)` are positive). Sparse or hashed storage would
   cost more than it saves, and pruning dead ends gains at most ~1/3.
4. **Locality kernel.** For an off-diagonal row (`L` fixed, `R` running), removing a
   left panel or the middle panel reads a predecessor row *in lock step* (streamed
   sequentially). Removing a right panel reads one predecessor row of length
   `≤ C(h, h/2)` (≤ 200 KB, stays in L2).
5. **Exactness.** `g(T) ≤ |T|!`, so `u64` words are exact for layers `k ≤ 20` (every
   `N ≤ 41`). The final sum is `u128`. For memory, `--mod32 Q` and `--mod16 Q` store
   residues (u32 or u16 words) and reconstruct with Garner CRT. Use one modulus more
   than needed: the tool checks that dropping the last residue gives the same value
   ("stable: verified").
6. **Memory hygiene.** There are two buffers the size of the largest layer, used
   alternately, plus `MADV_HUGEPAGE`. First-touch page faults are very expensive on this
   VM (≈ 2–10 s per GB).

**Complexity:** time `Θ(Σ_{k≤N/2} k·C(N,k)/2) ≈ N·2^N/8` predecessor checks.
Memory is `≈ C(N,⌊N/2⌋)` words (two layers, each halved by the mirror). Each step of
`N` costs ≈ ×2.2 in time.

Peak memory: N=32 4.8 GB (u64), N=33 9.3 GB (u64), N=34 9.4 GB (u32),
N=35 9.1 GB (u16). With `--blocks` (below): N=33 6.5 GB (u64), N=36 6.23 GB (u8),
N=37 11.2 GB (u8).

### Speedups measured (N=30 unless noted, this machine)

| version | time |
|---|---|
| `experiments/semi.c` (plain 2^N DP, u128, 1 thread), N=28 | 44.6 s, 4.3 GB |
| this crate, N=28, 3 threads | 1.7 s, ~0.3 GB |
| generic pull kernel, 3 threads | 11.7 s |
| + streaming off-diagonal kernel | 10.4 s |
| + 4 threads, buffer reuse | 7.0 s |

On N=28 that is ~25× faster than the plain DP and uses ~15× less memory. The remaining
cost is mostly memory latency, plus system time for page faults.

## Block streaming (`--blocks`, `block.rs`)

The plain layered DP holds two full layers (`k-1` and `k`) at the same time.
`--blocks` lowers this with three observations about the block structure
`(i=|L|, j=|R|, c)` of a layer:

1. **Locality in `i`.** Output block `(i, j, c)` of layer `k` reads only the blocks
   `(i-1, j, c)`, `(i, j-1, c)` (for `j = i` this is the mirror of `(i-1, i, c)`) and
   `(i, j, 0)` of layer `k-1`. All of these have `L`-size `i-1` or `i`. The output
   blocks are computed one at a time. Any order is correct; the order is
   increasing or decreasing `i`, improved by a deterministic local search
   (100k insertion moves) on the simulated peak. A block of layer `k-1` is released
   right after the last output block that reads it. Each layer is one
   `mmap(MAP_NORESERVE)` region, so only written pages count. A released block gets
   `MADV_DONTNEED` + `PROT_NONE`, so a stray read faults instead of returning a
   wrong value.
2. **Even `N`: the middle layer is never stored.** Complementing maps block
   `(i, h-i)` of layer `h = N/2` to itself (`|~L| = h-i`, `|~R| = i`), via
   `(rank L, rank R) ↦ (C-1-rank R, C-1-rank L)`, because complement reverses colex
   order. So each block of the middle layer is computed, combined with itself
   (`Σ g(S) g(S^c)`) and dropped.
3. **Odd `N` (fused form `Σ_{|U|=k+1} g(U) g(U^c)`).** The complement of block
   `(i, j, c)` of layer `k+1` is block `(i+c-1, h-i, 1-c)` of layer `k`, again with
   `L`-size `i-1` or `i`. Layer `k+1` exists only as 16-row tiles, and layer `k` is
   released as it is consumed.

**Memory model.** For each step, peak = max over the block order of
(live blocks of layer `k-1`) + (blocks of layer `k` written so far; in the final step,
only the current one). `folds peak N` prints the maximum over all steps. Sizes are in
words (multiply by the bytes per residue):

| N | old: layers h-1 and h | `--blocks` |
|---|---|---|
| 33 | 1.10e9 | 0.74e9 |
| 34 | 2.27e9 | 1.58e9 |
| 35 | 4.30e9 | 2.88e9 |
| 36 | 8.84e9 | 6.22e9 |
| 37 | 16.8e9 | 11.2e9 |
| 38 | 34.5e9 | 24.2e9 |

The peak is about one full layer plus the two or three largest blocks next to the
diagonal. For N=36, the binding step is 16 → 17, and block `(8,9)` alone is half of
layer 17. The measured `VmHWM` matches the simulation: for N=33 with u64, both were
6.52 GB before the local search, against 9.3 GB for the old code. For N=36 with u8,
both are 6.22 GB. The local search mostly helps odd N (N=37: 12.2e9 with plain
decreasing `i`). A global schedule over the (layer, block) DAG (interleaving blocks of
different layers, found by a greedy search) reaches 6.0e9 for N=36 and 10.6e9 for
N=37, so it was not implemented. No block order can go
below max over blocks of (block + the blocks it reads), which is 5.4e9 for N=36.

**Kernels.** The block path also has kernels that are kinder to the cache. They are
used only there:
* Diagonal blocks `(i, i, c)` are computed in 64-row tiles, walked column by column.
  The row kernel read `g(L\x, R)` at column `rank R` of a different row for every
  `x`: one cache miss per read. The tile reads 64 consecutive words instead.
* Off-diagonal blocks `(i, i+1, c)` are the largest blocks (half of layer 17 for
  N=36). There, removing a right panel lands in the *triangle* `(i, i, c)`, and half
  of these reads fall in a different row. These blocks get 16-row tiles.
* Barrett reduction replaces a 64-bit `div` per entry. Accumulators are `u64` and the
  validity masks are branch-free. Precomputed per-`j` tables give `rev` and
  `rank(R minus one bit)` by sequential reads, instead of random reads of 1 MB tables.
* The complement index in the final step is computed directly, with no table lookups.

On the shared machine (load 8–13 from other jobs) the user time for N=32 fell by
about 7%. This VM is limited by memory latency and by CPU share, not by instruction
count.

`folds check` runs the block path (`u64`, `u16`, `u8`) against all the other paths
for N ≤ 24. Debug builds also assert the direct complement indices.

## Sub-blocks (`--sub T`, `sub.rs`)

Block streaming cannot go below about 1.4 layers, because single blocks next to
the diagonal are half a layer. `--sub T` splits every block further and schedules
the pieces across layers.

**Layout.** Let `a = h - T`. `L` is split into `Llo` (panels `0..a`) and `HL` (the `T`
panels next to the middle), and `R` likewise into `Rlo` and `HR`. A *sub-block*
`(c, HL, HR, il = |Llo|, jl = |Rlo|)` holds all sets with these exact high parts and
these low popcounts, as a `C(a,il) × C(a,jl)` matrix (row = colex rank of `Llo`,
column = colex rank of `Rlo`). The mirror swaps `(il, HL) ↔ (jl, HR)`. The stored
representative has `(il, HL) ≤ (jl, HR)`, and when they are equal it is a triangle.
`T = 0` is exactly the block layout. Sub-blocks start on page boundaries, so freeing
one returns all of its pages. For N=38 and `T = 4` there are 32896 sub-blocks of at
most `C(15,7)² = 41 MB`.

**Dependencies.** The pull into sub-block `X` reads at most `2T + 3` sub-blocks of the
previous layer: `(il-1)` (remove a low left panel: row `rank(Llo\x)`), `(jl-1)`
(remove a low right panel: column `rank(Rlo\y)`), `HL\x` and `HR\y` (remove a high
panel: *same* row and column), and `c = 0` (remove the middle panel). Any of them
may be stored transposed or as a triangle. A small accessor handles this, and the
kernel walks 32-row tiles column by column, so every orientation reads consecutive
or row-local words.

**Final step.** For even `N`, the complement of sub-block `X` of the middle layer is
the sub-block `Y = (0, ~HR, ~HL, a-jl, a-il)` (canonicalized), and entry
`(rank Llo, rank Rlo)` maps to `(C-1-rank Llo, C-1-rank Rlo)`. One final job computes
`X` and `Y` from layer `h-1` into scratch buffers, adds `Σ w g(S) g(S^c)` (twice if
`X ≠ Y`), and drops both. For odd `N` the fused form is used as before: sub-block `U`
of layer `h+1` is computed in a buffer and multiplied with the stored complement
sub-block of layer `h`.

**Schedule.** The jobs form a DAG over all layers. A greedy list schedule
(`sub::plan`) runs, at each step, the ready job that minimizes (words written) −
(words freed right after it) − ¼ of each input it partly uses up. It interleaves
layers freely: final jobs start long before the last stored layer is finished. A
sub-block is freed right after its last reader. `folds peak N` prints the simulated
peak in words, and `folds subpeak N T [global] [caps]` compares variants:

| N | `--blocks` | `--sub 4` | largest stored layer |
|---|---|---|---|
| 33 | 0.74e9 | 0.63e9 | 0.58e9 |
| 34 | 1.58e9 | 1.11e9 | 1.10e9 |
| 35 | 2.88e9 | 2.36e9 | 2.27e9 |
| 36 | 6.22e9 | 4.54e9 | 4.30e9 |
| 37 | 11.2e9 | 9.77e9 | 8.84e9 |
| 38 | 24.2e9 | 16.8e9 | 16.8e9 |
| 39 | 43.6e9 | 35.6e9 | 34.5e9 |
| 40 | 94.8e9 | 66.7e9 | 65.6e9 |

The peak is now about one layer, the largest one stored (`h-1` for even N, `h` for
odd N). `T = 2..6`, layered or global, and three greedy variants all give
16.8–17.6e9 for N=38. One layer seems to be the floor for any order that never
recomputes: the final step pairs every set with its complement, and a schedule
reaches the two ends of each pair at opposite ends of its sweep. Measured RSS matches
the simulation: N=33 u8 0.70 GB against 0.63e9 words plus tables.

**Spilling with a fixed memory budget.** With `FOLDS_SPILL=<dir>`, each layer has an
anonymous region and a sparse file region. `sub::assign` places each sub-block in one
of them so that the anonymous total stays `≤ FOLDS_ANON` GB (default 7) at every
step. It first covers the steps whose live total is above a target file peak `F`,
choosing the live sub-blocks freed soonest. It then adds the rest by increasing
lifetime while they fit, to cut I/O. The smallest feasible `F` is found by bisection,
which gives `F ≈ peak − cap`. For N=38 with `FOLDS_ANON=3.5`, the result is 3.5 GB
anonymous + 13.4 GB file, with 40 GB written to the file per run.
* After a file-backed sub-block is written, it gets `sync_file_range` (start
  writeback) and `MADV_DONTNEED` (drop our mapping; the data stays in the page cache).
  So the process RSS is about the anonymous part, and the cached pages are clean and
  cheap for the kernel to drop.
* File-backed inputs get `MADV_WILLNEED` before each job.
* Freed sub-blocks are hole-punched, so disk use follows the live file set.

**Guards** (for a memory cgroup shared with other jobs):
* Before a job that grows anonymous memory, the run waits while `total_rss` of the
  cgroup (all anonymous memory of all its processes) + the growth +
  `FOLDS_HEADROOM` GB (default 1.5) is above the cgroup limit.
* Before writing to the spill file, it waits while the free disk space is below the
  write + `FOLDS_DISK_MIN` GB (default 2). A full disk would `SIGBUS` the mapping.

Waits are logged (`guard: ...`).

**Fast kernel.** Removing a low panel `x ≤ x0 = ⌊(N-1-a)/2⌋` has a window `(x, 2x]`
(resp. its mirror) that meets the other side only in high panels, which are fixed for
the sub-block. So its validity depends on the row alone (left) or the column alone
(right). Rows of `pa` (the `(il-1)` sub-block) for valid `x ≤ x0` are added with a
vectorized `u32` row add. For right removals `y ≤ x0`, only the valid ones are read,
and validity is tested per entry only for the rest (N=38, `T=4`: 3 of 15 low panels per
side, plus the high panels and the middle panel). This is 1.7× faster than the
entry-by-entry kernel, and 32-row tiles gain another 13%. The fast kernel runs for
words of ≤ 16 bits (`FOLDS_SLOW=1` turns it off). Triangle sub-blocks (0.8% of the
entries) use the generic kernel.

`folds check` runs `--sub` with `T = 0, 1, 4` (u64), `T = 3` (u8 CRT) and `T = 2`
(u16 CRT) against all other paths for N ≤ 24. A spilled run with a tiny anonymous
cap reproduces N = 2..27 with 12 u8 moduli.

## Validation (`folds check`)

For both rules: permutation brute force from the literal definition (N ≤ 9), plain
subset DP (N ≤ 20), MITM u64, MITM u32-CRT and u16-CRT (N ≤ 18), all against each
other and against the known terms. These are `experiments/semi_counts.txt` for N ≤ 27,
and **A003407 for the symmetric rule** (all 14 listed terms match; MITM continues
the sequence with 74904, 212728, 368016, 659296, … up to N=24). The stats code (by-last,
prefix counts) is checked against the dense DP for N ≤ 12. `cargo test` checks the
fast validity test against the literal definition and checks that `index()` is a
bijection onto mirror orbits (N ≤ 13). a(28) was also reproduced independently with
`experiments/semi.c`. a(30), a(31) were reproduced by the u32 and u16 CRT paths. The block path reproduces
a(33) exactly (u64), a(33) mod 241, a(34) mod 251 and mod 65521, and a(29..32)
residues.

## Statistics (`folds stats semi N`)

This runs the full forward DP (all layers, u128, mirror-reduced; practical to N≈30) and prints:
* `prefixes(k)`: number of valid prefixes of length k, `Σ_{|S|=k} g(S)`
* `reachable_sets(k)`, `dead_end_sets(k)`: sets with `g>0`, and those among them with
  no valid next step
* `by_first = by_last(m)`: #sequences starting with m (= #sequences ending with m, by reversal)
* `by_first2[m][x]`: #sequences starting with `m, x`

### Observations (formula hunting)

These are fitted to data, not proven.
* `prefixes(1) = N` and `prefixes(2) = ⌊N²/2⌋`.
* `prefixes(3)` (checked with a separate DFS for N ≤ 90) is a quasi-polynomial of
  **period 6**: `(2/9)N³ − N²/12 − αN + β`. Here `α = 5/6` for even N and `1/3` for odd
  N. `β` depends on `N mod 6`: 0, 7/36, 2/9, −1/4, 4/9, −1/36 for residues 0..5. The
  mod-3 dependence is consistent with a(N) running above trend when 3 | N: the ratio
  a(N)/a(N−1) jumps at N = 21, 24, 27, 30, 33.
* `prefixes(4)` has no quasi-polynomial fit with period ≤ 9 (N ≤ 70).
* Dead-end sets (no valid next step) occur almost only at even `|S|`.
* Every sequence starting `1, N` (N even) is doomed. The second step after `1` must be
  `> N/2`.
* `by_first(m)` is mirror symmetric (as it must be) and increases toward the middle.

## Timings (4 threads, 15 GB VM; see `results/semi.txt`)

| N | a(N) | time | storage |
|---|---|---|---|
| 28 | 3603074636066234798 | 1.7 s | u64 |
| 29 | 27545080998591561856 | 5.0 s | u64 |
| 30 | 262878496654501774250 | 7.0 s | u64 |
| 31 | 2037247307316034896720 | 16 s | u64 |
| 32 | 20222490725552617395966 | 27 s | u64 |
| 33 | 171668579369815966705184 | 74 s | u64, 9.3 GB |
| 34 | 1711977358970374039688092 | 4 × ~125 s | u32 CRT, 9.4 GB |
| 35 | 14916356465581456801127844 | 7 × 313–755 s | u16 CRT, 9.1 GB, machine under load |
| 36 | 162918548122441960881265188 | 13 × 438–2137 s | u8 CRT, `--blocks`, 6.23 GB |
| 37 | 1435459602925600924848243286 | 13 × 1055–1511 s | u8 CRT, `--blocks`, 11.2 GB, `FOLDS_SPILL` |
| 38 | 15884954204816776206921874682 | 14 × 602–2003 s | u8 CRT, `--sub 4`, 3.5 GB anon + 13.4 GB file, RSS ≤ 3.98 GB |

**Largest N reached: 38.** All new terms have a redundant CRT modulus that agrees
(N=36 also a second one, mod 181; N=38 has two: the 12 moduli up to 193 already give
the value, and both mod 191 and mod 181 agree). All satisfy the mod-4 law
a ≡ c (mod 4): a(36) ≡ 0, a(37) ≡ 2, a(38) ≡ 2 (c(38) = 301305621655490 ≡ 2).
The `--sub` path also reproduced a(36) mod 251 = 102 and a(37) mod 241 = 240, both
with spilling (`results/n36_sub.log`, `results/n37_sub.log`).

The stats files `results/stats/semi_N.txt` (N = 2..24) also contain `alive_sets` /
`doomed_sets` (`g>0` and `f=0`; the `doomed_total` column reproduces the "dead ends"
1, 2, 4, 18, 30, 63, … of the top-level README).

## Wall

Memory is the limit. Memory × number of CRT runs is roughly constant: a(N) has about
2.9N bits, and one run gives `log2(modulus)` of them. Time per run is about the same
for every word size, because memory latency dominates it.

* **N=36** (`--blocks`, u8): the peak is 6.2e9 words. u16 would need 12.4 GB, which
  does not fit next to the other jobs. This took 13 u8 runs of 7–35 min each
  (depending on load), about 2.6 h in total.
* **N=37** (`--blocks`, u8, `FOLDS_SPILL`): the peak is 11.2e9 words. On this VM all
  tool processes share one memory cgroup with a 14.3 GB limit. One run on anonymous
  memory was OOM-killed, and the OOM also killed another job's process. The other
  runs map every layer of 1 GB or more from a sparse file in a scratch directory
  (`FOLDS_SPILL=<dir>`). The kernel can then write back and evict those pages
  instead of killing a process. Freed blocks are hole-punched, so disk use follows
  the live set (≤ 11.2 GB). Spilling was no slower here: each run took 18–25 min,
  with the I/O overlapped. 13 runs took about 4.5 h. During one run, another job's
  process grew to 13 GB. The spilled pages were evicted and re-read from disk, and
  the run finished normally.
* **N=38** (`--sub 4`, u8, `FOLDS_SPILL`, `FOLDS_ANON=3.5`): `--blocks` would peak at
  24.2e9 words, more than RAM + free disk here. Sub-blocks bring the live set down to
  16.8e9 words, about one layer (layer 18). Of this, 3.5 GB stays anonymous and up to
  13.4 GB lives in the spill file (≈ 40 GB written per run). The process RSS stayed
  at ≤ 3.98 GB. Each run took 10–33 min (load 4–6), which is faster than the old
  N=37 runs thanks to the row kernel. That is 14 runs, 4.6 h of run time in total. The memory
  guard waited only once. Runs interrupted by container restarts were simply rerun.
* **N=39**: `--sub 4` peaks at 35.6e9 words (layer 19 is 34.5e9; `T = 3, 5, 6` are no
  better). In u8 that is ≈ 36 GB live. With 3.5 GB anonymous memory it needs ≈ 32 GB of
  spill disk plus a margin, i.e. ≥ 36 GB free (this VM has 18), and ≈ 114 GB written
  per run. Alternatively, a ≥ 48 GB machine could hold it all in RAM. Expect ≈ 2.2×
  the N=38 time per run (30–70 min here). a(39) ≈ 2^97 fits in the 13 u8 moduli
  (101 bits), plus one redundant modulus, so 14 runs.
* Going below one layer would need recomputation. Every non-recomputing order of
  this DAG seems to need about one full layer live (see "Sub-blocks").
