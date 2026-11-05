"""Burnside / V4 orbit counts, mod-4 identity, and OEIS lookups."""
import json, subprocess, time
from data import a, load_selfdual

c = load_selfdual()
print("self-dual c(N):", [c[N] for N in sorted(c)])
orb = {}
for N in sorted(a):
    fixM = 1 if N == 1 else 0
    fixR = 1 if N == 1 else 0
    tot = a[N] + fixM + fixR + c[N]
    assert tot % 4 == 0
    orb[N] = tot // 4
    if N >= 2:
        assert c[N] % 2 == 0 and (a[N] - c[N]) % 4 == 0
print("V4 orbits:", [orb[N] for N in sorted(orb)])
print("a(N) == c(N) mod 4 for 2<=N<=33: OK")
print("a mod 4 :", [a[N] % 4 for N in sorted(a)])
print("c mod 4 :", [c[N] % 4 for N in sorted(a)])
print("c mod 8 :", [c[N] % 8 for N in sorted(c)])
print("v2(c)   :", [((c[N] & -c[N]).bit_length() - 1) if c[N] else None for N in sorted(c)])
print("a mod 8 vs c mod 8:", [(a[N] % 8, c[N] % 8) for N in sorted(a)])

ev = [c[N] for N in sorted(c) if N % 2 == 0]
od = [c[N] for N in sorted(c) if N % 4 == 1]
print("c(2n):", ev)
print("c(4n+1):", od)
print("ratios c(2n)/c(2n-2):", [round(ev[i] / ev[i - 1], 3) for i in range(1, len(ev))])
print("c(2n)^2/a(2n):", [round(c[N] ** 2 / a[N], 3) for N in sorted(a) if N % 2 == 0])
print("c(4n+1)/c(4n):", [round(c[N] / c[N - 1], 4) for N in sorted(c) if N % 4 == 1 and N > 1])


def oeis(seq):
    q = ",".join(map(str, seq))
    out = subprocess.run(["curl", "-s", f"https://oeis.org/search?q={q}&fmt=json"],
                         capture_output=True, text=True).stdout
    time.sleep(1)
    try:
        r = json.loads(out)
    except Exception:
        return "?"
    if not r:
        return "no match"
    return [f"A{x['number']:06d} {x['name'][:60]}" for x in r[:3]]


queries = {
    "c(N)": [c[N] for N in range(2, 16)],
    "c(N)/2": [c[N] // 2 for N in range(2, 16)],
    "c(2n)": ev[:10],
    "c(2n)/2": [x // 2 for x in ev[:10]],
    "c(4n+1)": od[:7],
    "orbits": [orb[N] for N in range(1, 14)],
    "orbits(N>=2)": [orb[N] for N in range(2, 14)],
    "a/2": [a[N] // 2 for N in range(2, 14)],
    "(a-c)/4": [(a[N] - c[N]) // 4 for N in range(2, 14)],
}
for k, s in queries.items():
    print(k, s, "->", oeis(s))
