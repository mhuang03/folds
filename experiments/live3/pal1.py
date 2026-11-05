"""pal1.py q [nu]: in the class convention of live2/PROOFS 2.2 (tau valid and sigma o tau valid,
sigma(t) = ((nu - t) mod q) + 1), list palindromic tau (tau_{q+1-i} = sigma(tau_i)) for each
start; prints the first one found per start."""
import sys


def arms(k, m):
    r = min(m - 1, k - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def valid_step(k, S, m):
    L, R = arms(k, m)
    return sum(1 for x in L if x in S) == sum(1 for x in R if x in S)


def valid(k, seq):
    S = set()
    for m in seq:
        if not valid_step(k, S, m):
            return False
        S.add(m)
    return True


def search(q, nu, t, allsol=False):
    sig = {x: (nu - x) % q + 1 for x in range(1, q + 1)}
    fix = [x for x in range(1, q + 1) if sig[x] == x]
    half = q // 2
    out = []

    def rec(seq, S):
        if len(seq) == half:
            full = seq + fix + [sig[x] for x in reversed(seq)]
            if len(full) == q and valid(q, full):
                out.append(full)
                return not allsol
            return False
        for m in range(1, q + 1):
            if m in S or sig[m] in S or sig[m] == m:
                continue
            if valid_step(q, S, m) and rec(seq + [m], S | {m}):
                return True
        return False

    if sig[t] != t:
        rec([t], {t})
    return out


if __name__ == '__main__':
    q = int(sys.argv[1])
    nu = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    for t in range(1, q + 1):
        r = search(q, nu, t, 'all' in sys.argv)
        print(t, len(r), r[:6])
