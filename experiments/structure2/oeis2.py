"""OEIS lookups for columns / diagonals of the refined triangles (semi and sym)."""
import json, subprocess, time, math
from common import counts, stats

a, s = counts()


def lookup(terms):
    q = ",".join(str(int(t)) for t in terms)
    out = subprocess.run(["curl", "-s", "-m", "30", f"https://oeis.org/search?q={q}&fmt=json"],
                         capture_output=True, text=True).stdout
    time.sleep(1.0)
    try:
        js = json.loads(out)
    except Exception:
        return ['? ' + out[:80]]
    if not js:
        return []
    if isinstance(js, dict):
        js = js.get('results') or []
    return ['A%06d %s' % (r['number'], r['name'][:70]) for r in js[:3]]


def seqs(rule, Nmax):
    D = {n: stats(n, rule) for n in range(2, Nmax + 1)}
    out = {}
    rng = range(2, Nmax + 1)
    for j in range(1, 4):
        out[f'F(N,{j})'] = [D[n]['F'][j - 1] for n in rng if n >= j]
    out['F(N,mid)'] = [D[n]['F'][(n + 1) // 2 - 1] for n in rng]
    out['F(2n+1,n+1)'] = [D[n]['F'][(n + 1) // 2 - 1] for n in rng if n % 2]
    out['F(N,N/2) even'] = [D[n]['F'][n // 2 - 1] for n in rng if n % 2 == 0]
    out['F(N,mid-1)'] = [D[n]['F'][(n + 1) // 2 - 2] for n in rng if n >= 3]
    out['F2(N,1,N)'] = [D[n]['F2'][0][n - 1] for n in rng]
    out['F2(N,1,N-1)'] = [D[n]['F2'][0][n - 2] for n in rng if n >= 3]
    out['F2(N,N/2+..) first nonzero after 1'] = [next(v for v in D[n]['F2'][0] if v) for n in rng]
    out['E-O first panel odd N'] = [sum(D[n]['F'][1::2]) - sum(D[n]['F'][0::2]) for n in rng if n % 2]
    out['T(N,N-2)'] = [D[n]['prefixes'][n - 2] for n in rng]
    out['T(N,N-3)'] = [D[n]['prefixes'][n - 3] for n in rng if n >= 3]
    out['T(N,N-2)-a(N)? (a - T(N,N-2))'] = [D[n]['total'] - D[n]['prefixes'][n - 2] for n in rng]
    out['reach total'] = [sum(D[n]['reach']) for n in rng]
    out['reach(N,N-2)'] = [D[n]['reach'][n - 2] for n in rng]
    out['reach(N,3)'] = [D[n]['reach'][3] for n in rng if n >= 3]
    out['reach(N,4)'] = [D[n]['reach'][4] for n in rng if n >= 4]
    out['reach(N,mid)'] = [D[n]['reach'][n // 2] for n in rng]
    out['dead total'] = [sum(D[n]['dead']) for n in rng]
    if 'alive' in D[2]:
        out['alive total'] = [sum(D[n]['alive']) for n in rng if n <= 26]
        out['alive(N,3)'] = [D[n]['alive'][3] for n in rng if 3 <= n <= 26]
    out['nonzero F2 count'] = [sum(1 for r in D[n]['F2'] for v in r if v) for n in rng]
    return out


if __name__ == '__main__':
    for rule, Nmax in (('semi', 30), ('sym', 28)):
        for name, v in seqs(rule, Nmax).items():
            v = [x for x in v]
            # skip leading zeros/ones, use up to 20 terms
            while v and v[0] in (0, 1):
                v = v[1:]
            res = lookup(v[:20]) if len(v) >= 5 else ['(too short)']
            # also try halved sequence when all even
            if not res and all(x % 2 == 0 for x in v):
                res = ['halved: ' + r for r in lookup([x // 2 for x in v[:20]])]
            print(f'{rule:4s} {name:34s} {v[:8]} ->', res if res else 'no match', flush=True)
