"""palcert.py q1 q2 [skip]: palindromic certificates (q, nu, t0, x) for Folds/Live4.lean
(`palOK`, `goodL_palin`): x and sig o x valid from scratch in the q-strip, t0 = fixed point of
sig balanced by x, x + t0 + sig x = [q].  One x per start x_1, for every odd q in [q1, q2] and
every nu; with 'skip', starts already good in the closure without certificates
(covlean4.good_set) are skipped, and only one of t, sig(t) is kept (the closure adds sig).
Output: Lean list literal entries, one per line, and a summary on stderr."""
import sys
from palnu import win, bal

q1, q2 = int(sys.argv[1]), int(sys.argv[2])
skip = len(sys.argv) > 3
if skip:
    import covlean4


def certs(q, nu):
    L, R = win(q)
    sg = [0] + [(nu - t) % q + 1 for t in range(1, q + 1)]
    t0 = [t for t in range(1, q + 1) if sg[t] == t][0]
    k = (q - 1) // 2
    memo = {}

    def fin(S, T, cnt):
        if cnt == k:
            return [] if bal(S, t0, L, R) else None
        if S in memo:
            return memo[S]
        res = None
        for t in range(1, q + 1):
            if t == t0 or (S >> t & 1) or (T >> t & 1):
                continue
            if bal(S, t, L, R) and bal(T, sg[t], L, R):
                rest = fin(S | 1 << t, T | 1 << sg[t], cnt + 1)
                if rest is not None:
                    res = [t] + rest
                    break
        memo[S] = res
        return res

    out = {}
    for t in range(1, q + 1):
        if t == t0:
            continue
        r = fin(1 << t, 1 << sg[t], 1)
        if r is not None:
            out[t] = (t0, [t] + r)
    return out, sg


lines = []
for q in range(q1, q2 + 1):
    if q % 2 == 0:
        continue
    have = covlean4.good_set(q) if skip else set()
    n = 0
    for nu in range(q):
        out, sg = certs(q, nu)
        done = set()
        for t, (t0, x) in sorted(out.items()):
            if (nu, t) in have or t in done:
                continue
            done.add(t)
            done.add(sg[t])
            lines.append('(%d,%d,%d,[%s])' % (q, nu, t0, ','.join(map(str, x))))
            n += 1
    print('q', q, 'certificates', n, file=sys.stderr)
print('[' + ',\n  '.join(lines) + ']')
