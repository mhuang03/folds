# For each prime p in {13,17,19,23} and each nu < p, choose a Live4 certificate
# cert_p_i : fullOK (p, nu', _) with nu' = nu (direct) or nu' = p - nu (mirror),
# and print the Lean proof of `AllH p` (pasted into Folds/SuperExp7.lean).
import re, sys
src = open(sys.argv[1]).read()
certs = re.findall(r"theorem (cert_\d+_\d+) : fullOK \((\d+), (\d+),", src)
by = {}
for name, q, nu in certs:
    by.setdefault((int(q), int(nu)), name)
for p in [13, 17, 19, 23]:
    out = [f"theorem allH_{p} : AllH {p} := by", "  intro ν hν", "  interval_cases ν"]
    for nu in range(p):
        if nu == 0:
            out.append("  · exact hypH_zero (by norm_num)")
        elif nu == 1:
            out.append("  · exact hypH_one (by norm_num)")
        elif nu == p - 1:
            out.append(f"  · exact hypH_neg_one (q := {p}) (by norm_num)")
        elif (p, nu) in by:
            out.append(f"  · exact hypH_of_fullOK {by[(p, nu)]}")
        elif (p, p - nu) in by:
            out.append(f"  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num)"
                       f" (hypH_of_fullOK {by[(p, p - nu)]})")
        else:
            raise SystemExit(f"missing {p} {nu}")
    print("\n".join(out)); print()
