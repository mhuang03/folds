# mklean.py: turn gen.c witnesses into Lean certificates for Folds/Live3p.lean.
#   python3 mklean.py N1 N2 ...  > fragment.lean
# Each table entry is (a + 32 b + 1024 c, sum_i w_i 64^i): the sorted triple and its ordering
# w of [N] \ {a, b, c} from scratch, packed in base 64 (decoded by `digits64` in Lean).
# Kernel checks are split into small `decide +kernel` goals (table chunks of CH entries, one
# coverage goal per first step x) to keep the kernel's memory low.
import subprocess, sys
sys.set_int_max_str_digits(100000)

CH = 30

def entries(N):
    out = subprocess.run(['./gen', str(N)], capture_output=True, text=True, check=True).stdout
    res = []
    for line in out.split('\n'):
        if not line.startswith('W '): continue
        t = list(map(int, line.split()[1:]))
        assert t[0] == N
        a, b, c, w = t[1], t[2], t[3], t[4:]
        assert len(w) == N - 3 and 1 <= a < b < c <= N < 32
        code = sum(x * 64 ** i for i, x in enumerate(w))
        res.append((a + 32 * b + 1024 * c, code))
    return res

def emit(N):
    es = entries(N)
    chunks = [es[i:i + CH] for i in range(0, len(es), CH)] or [[]]
    names = [f"tbl{N}_{i}" for i in range(len(chunks))]
    print(f"/-! ### `N = {N}`: {len(es)} witness orderings -/")
    print()
    for nm, ch in zip(names, chunks):
        print(f"def {nm} : List (Nat × Nat) := [")
        print(",\n".join(f"  ({k}, {c})" for k, c in ch) + "]")
        print()
        print(f"theorem {nm}_ok : tblOK {N} {nm} = true := by decide +kernel")
        print()
    print(f"def tbl{N} : List (Nat × Nat) := " + " ++ ".join(names))
    print()
    mask = 0
    for k, _ in es: mask |= 1 << k
    print(f"def mask{N} : Nat := {mask}")
    print()
    print(f"theorem mask{N}_eq : maskL 0 (tbl{N}.map Prod.fst) = mask{N} := by decide +kernel")
    print()
    for x in range(1, N + 1):
        print(f"theorem cov{N}_{x} : coverX {N} mask{N} {x} = true := by decide +kernel")
    print()
    print(f"theorem cert{N} : Cert {N} tbl{N} := by")
    lem = [f"tbl{N}"] + (["tblOK_append"] if len(names) > 1 else []) + \
        [f"{nm}_ok" for nm in names] + (["Bool.and_self"] if len(names) > 1 else [])
    print(f"  refine ⟨by simp only [" + ", ".join(lem) + "], fun x h1 h2 => ?_⟩")
    print(f"  rw [mask{N}_eq]")
    print("  interval_cases x")
    print("  exacts [" + ", ".join(f"cov{N}_{x}" for x in range(1, N + 1)) + "]")
    print()

for N in map(int, sys.argv[1:]):
    emit(N)
