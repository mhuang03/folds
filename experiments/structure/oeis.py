"""Tiny OEIS lookup helper: python3 oeis.py 1,2,3,...  (or import lookup)."""
import json, subprocess, sys, time


def lookup(seq, n=6):
    """Return list of (A-number, name) for sequences matching `seq` (list of ints)."""
    terms = [int(x) for x in seq]
    # drop leading trivial terms which OEIS handles poorly
    q = ",".join(map(str, terms))
    out = subprocess.run(["curl", "-s", f"https://oeis.org/search?q={q}&fmt=json"],
                         capture_output=True, text=True).stdout
    time.sleep(0.5)
    try:
        js = json.loads(out)
    except Exception:
        return [("?", out[:200])]
    if not js:
        return []
    if isinstance(js, dict):
        js = js.get("results") or []
    return [("A%06d" % r["number"], r["name"]) for r in js[:n]]


if __name__ == "__main__":
    for r in lookup(sys.argv[1].split(",")):
        print(*r)
