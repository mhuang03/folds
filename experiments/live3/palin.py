"""palin.py q1 q2: rotation-stable sequences of the q-strip of the PALINDROMIC form
tau_{q+1-i} = iota(tau_i), iota = mirror o rot_nu (an involution), so that rot_nu(tau) is the
mirror of reversed tau and hence valid as soon as tau is.  Prints the (nu, t) for which no such
tau with tau_1 = t exists (q odd: iota has exactly one fixed point, the middle step)."""
import sys


def arms(k, m):
    r = min(m - 1, k - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def valid_step(k, S, m):
    L, R = arms(k, m)
    return sum(1 for x in L if x in S) == sum(1 for x in R if x in S)


def search(q, nu, t):
    iota = {x: (q + 1) - ((x - 1 + nu) % q + 1) for x in range(1, q + 1)}
    iota = {x: (v if v >= 1 else v + q) for x, v in iota.items()}
    half = q // 2

    def finish(seq):
        S = set(seq)
        rest = [x for x in range(1, q + 1) if x not in S and iota[x] == x] if q % 2 else []
        full = list(seq) + rest + [iota[x] for x in reversed(seq)]
        S = set()
        for m in full:
            if not valid_step(q, S, m):
                return None
            S.add(m)
        return full

    def rec(seq, S):
        if len(seq) == half:
            return finish(seq)
        for m in range(1, q + 1):
            if m in S or iota[m] in S or iota[m] == m:
                continue
            if not valid_step(q, S, m):
                continue
            r = rec(seq + [m], S | {m})
            if r:
                return r
        return None

    if iota[t] == t:
        return None
    return rec([t], {t}) if valid_step(q, set(), t) else None


if __name__ == '__main__':
    for q in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        bad = []
        for nu in range(q):
            for t in range(1, q + 1):
                if not search(q, nu, t):
                    bad.append((nu, t))
        print(q, bad, flush=True)
