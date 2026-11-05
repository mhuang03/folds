# `folds`: fast counting of semi-symmetric fold sequences

The problem statement and the reformulations are in the top-level `README.md`. In
this crate, panels are 0-indexed bits `p = m-1` of a `u64` mask. `g(S)` is the number
of valid orderings that build the set `S`.

```
cargo run --release -- semi 1 33              # prints "N a(N) time" for N = 1..33
cargo run --release -- sym 1 24               # symmetric variant (OEIS A003407)
cargo run --release -- semi 34 --mod32 4      # u32 residues, 4 moduli + CRT (half memory)
cargo run --release -- semi 35 --mod16 7      # u16 residues (quarter memory)
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
   a time.
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
N=35 9.1 GB (u16).

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

## Validation (`folds check`)

For both rules: permutation brute force from the literal definition (N ≤ 9), plain
subset DP (N ≤ 20), MITM u64, MITM u32-CRT and u16-CRT (N ≤ 18), all against each
other and against the known terms. These are `experiments/semi_counts.txt` for N ≤ 27,
and **A003407 for the symmetric rule** (all 14 listed terms match; MITM continues
the sequence with 74904, 212728, 368016, 659296, … up to N=24). The stats code (by-last,
prefix counts) is checked against the dense DP for N ≤ 12. `cargo test` checks the
fast validity test against the literal definition and checks that `index()` is a
bijection onto mirror orbits (N ≤ 13). a(28) was also reproduced independently with
`experiments/semi.c`. a(30), a(31) were reproduced by the u32 and u16 CRT paths.

## Statistics (`folds stats semi N`)

This runs the full forward DP (all layers, u128, mirror-reduced; practical to N≈30) and prints:
* `prefixes(k)`: number of valid prefixes of length k, `Σ_{|S|=k} g(S)`
* `reachable_sets(k)`, `dead_end_sets(k)`: sets with `g>0`, and those among them with
  no valid next step
* `by_first = by_last(m)`: #sequences starting with m (= #sequences ending with m, by reversal)
* `by_first2[m][x]`: #sequences starting with `m, x`

## Wall

Memory is the limit. The middle layer has `C(N, N/2)/2` orbits.
* N=35 needs u16 residues (7 runs).
* N=36 has 4.5e9 orbits in the middle layer plus 4.3e9 in the previous one. Even u16
  gives 17.5 GB. It would need u8 residues (~12 runs of ~25 min each), or
  block-wise freeing of the previous layer combined with streaming the final
  combination. For even N the complement maps every block `(i,j)` of the middle layer
  to itself, so the middle layer never has to be stored whole. Or it would need a
  machine with ≥ 32 GB.
