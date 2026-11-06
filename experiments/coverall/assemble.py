"""assemble.py: build Folds/CoverAll.lean from the parts in experiments/coverall/lean/ and the
generated code (cells: genlean.py, leaves: genbulk.py, thin sets: genthin.py if present).

python3 assemble.py [--regen]
"""
import os, sys, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', '..', 'Folds', 'CoverAll.lean')

DOC = '''import Folds.Residual

/-!
# The covering statement `CoverAll`: explicit certificates on a cell decomposition

`experiments/coverall/PROOFS.txt`.

`Residual.CoverAll N` says that every mixed-parity wide non-special pair `(u, u')` lies in
`Proven2` (old regions, `RegionPF`, `RegionSL`, `RegionS`).  Here:

* `parOK_edge4`, `parOK_edge1`: **edge certificates**.  For a family and a lattice direction
  `w₁ = (p, q)`, the witness polygon contains the fundamental parallelogram whose two corners on the
  inner and outer lattice lines lie on one edge of the strip (`U2 - L1 = 1`, resp. `U1 - L2 = 1`),
  the outer one as high as both tops allow; this reduces `ParOK` to four "key" inequalities in the
  edge parameter.
* `KeyA`, `KeyB4`, `KeyB1`: the cells `Z` in orientation `(u', u)` with `w₁ = (1,1)`, `(2,1)`;
  their key conditions are explicit polynomials in `(N, u, u')` (`parOK_of_keyA` ...).
* `leaf_*`: on eleven polyhedra ("leaves") in `(N, u, u')` the key polynomials (or the polynomial
  conditions of the old regions `D`, `B`: `regionD_of_polys`, `regionB_of_polys`) are nonnegative;
  each proof is `linarith` with explicit products of the leaf's linear constraints (a
  Handelman-type certificate found by LP, `experiments/coverall/leaves.py`).
* `bulk`: outside the thin sets `Thin` (the diagonal strip `u' ≤ u + 9`, the strip
  `|u' - 2u| ≲ 15` above `u ≈ N/8`, a bounded cluster at `(N/4, 3N/8)` on the edge, `u ≤ 3`),
  every pair of the triangle is in `Proven` or `ParOK (consZ N u' u)`.
* `d1_line`: the line `u' = u + 1` (`5 ≤ u ≤ (N - 21)/3`) by an explicit slice certificate
  (`RegionSL`: `X(N, s, 0)`, orientation `(u', u)`, slice `a = c + 1`, sides `(1, 0)`, `(δ, 1)`).
* `coverAll_of_thinCover`, `conjectureC_of_thinCover`: `CoverAll N` (hence Conjecture C) for all
  `N > 300` follows from the statement `ThinCover` about the remaining thin sets `ThinRest`
  (**not proven**: the diagonal strip `u' ≤ u + 9` except the bulk of the line `d = 1`, the strip
  `u' - 2u ∈ [-12, 15]` above `u ≈ N/8`, the cluster at `(N/4, 3N/8)`, `u ≤ 3`; numerically only
  `d ∈ {0, 1, 2, 3}`, `u' - 2u ∈ [-9, 7]` and a few cluster points there need slices, see
  `experiments/coverall/PROOFS.txt`).
-/

namespace Folds
namespace CoverAll

open Residual Live2 Live8 ArithCover

'''

PARTS = ['edge', 'CELLS', 'oldreg', 'LEAVES', 'bulkthm', 'gen_d1', 'reduct']


def main():
    regen = '--regen' in sys.argv
    if regen:
        subprocess.run([sys.executable, os.path.join(HERE, 'genlean.py'), os.path.join(HERE, 'lean', 'gen_cells.lean')], check=True, cwd=HERE)
        subprocess.run([sys.executable, os.path.join(HERE, 'genbulk.py'), os.path.join(HERE, 'lean', 'gen_leaves.lean')], check=True, cwd=HERE)
    out = DOC
    for p in PARTS:
        if p == 'CELLS':
            s = open(os.path.join(HERE, 'lean', 'gen_cells.lean')).read()
            s = s.split('open Folds.Residual\n', 1)[1].rsplit('end Folds.CoverAll', 1)[0]
        elif p == 'LEAVES':
            s = open(os.path.join(HERE, 'lean', 'gen_leaves.lean')).read()
        elif p == 'THIN':
            f = os.path.join(HERE, 'lean', 'gen_thin.lean')
            if not os.path.exists(f):
                continue
            s = open(f).read()
        else:
            s = open(os.path.join(HERE, 'lean', p + '.lean')).read()
        out += s.strip() + '\n\n'
    out += 'end CoverAll\nend Folds\n'
    open(OUT, 'w').write(out)


main()
