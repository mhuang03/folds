"""oeis_lookup.py: look up every sequence derived from the W(N,k) tables in the OEIS.

  python3 oeis_lookup.py > oeis_out.txt

Uses the public JSON search (https://oeis.org/search?q=...&fmt=json) with a generic client.
For each sequence the query is the terms from the first index where it is "interesting"
(at most 12 terms, dropping leading terms <= 1).  Prints the A-numbers and names of the hits
(at most 4), or 'no match'.
"""
import json, subprocess, sys, time
from analyze import load, A_val

W = load()


def query(terms):
    q = ','.join(str(t) for t in terms)
    url = 'https://oeis.org/search?q=%s&fmt=json' % q
    for attempt in range(3):
        try:
            out = subprocess.run(['curl', '-sS', '-m', '40', url], capture_output=True, text=True).stdout
            res = json.loads(out)
            if res is None:
                return []
            if isinstance(res, dict):
                res = res.get('results') or []
            return [('A%06d' % r['number'], r['name']) for r in res[:4]]
        except Exception as e:
            time.sleep(3)
    return None


def trim(seq, n=12):
    s = list(seq)
    while len(s) > 6 and abs(s[0]) <= 1:
        s = s[1:]
    return s[:n]


def main():
    seqs = []
    for (conv, kind), T in sorted(W.items()):
        Ns = sorted(T)
        tag = '%s/%s' % (conv, kind)
        seqs.append((tag + ' row sums', [sum(T[N]) for N in Ns]))
        seqs.append((tag + ' |chi| = |A_N(-1)|', [abs(sum((-1) ** k * T[N][k] for k in range(1, N + 1))) for N in Ns]))
        seqs.append((tag + ' |A_N(-2)|', [abs(A_val(T[N], -2)) for N in Ns]))
        seqs.append((tag + ' A_N(2)', [A_val(T[N], 2) for N in Ns]))
        seqs.append((tag + ' A_N(3)', [A_val(T[N], 3) for N in Ns]))
        for k in (2, 3, 4):
            seqs.append((tag + ' column k=%d' % k, [T[N][k] for N in Ns if N >= k]))
        for j in (1, 2):
            seqs.append((tag + ' diagonal W(N,N-%d)' % j, [T[N][N - j] for N in Ns if N - j >= 1]))
    # odd-N Euler characteristic of (a)
    Ta = W[('a', 'semi')]
    seqs.append(('a/semi chi at odd N', [sum((-1) ** (N - k) * Ta[N][k] for k in range(1, N + 1)) for N in sorted(Ta) if N % 2]))
    seen = {}
    for name, s in seqs:
        t = trim(s)
        if len(set(t)) <= 1 or all(abs(x) <= 1 for x in t):
            print('%-34s %s\n      (trivial, skipped)' % (name, t))
            continue
        key = tuple(t)
        if key not in seen:
            seen[key] = query(t)
            time.sleep(1.0)
        hits = seen[key]
        print('%-34s %s' % (name, t))
        if hits is None:
            print('      LOOKUP FAILED')
        elif not hits:
            print('      no match')
        else:
            for a, nm in hits:
                print('      %s  %s' % (a, nm[:110]))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
