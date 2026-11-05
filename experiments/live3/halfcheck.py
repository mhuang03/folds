"""halfcheck.py q1 q2: checks Theorem H and the families (E), (O) of PROOFS.txt (live3) 1.3:
for odd q, the palindromic orders pi = U+1 ++ [1] ++ sigma(rev U) built from Lemma W satisfy the
chain condition ChainOK q 1 pi (computed directly from CycBal), for every start t = 3 (mod 4)
and t = q - 1 (mod 4).  Prints the starts covered per q (and any failure)."""
import sys


def cycbal(q, A, s, rho):
    """CycBal of live2/Live2.lean, in the counting form (rho < q)."""
    L = sum(1 for t in A if 1 <= (s - t) % q <= rho)
    R = sum(1 for t in A if 1 <= (t - s) % q <= rho)
    return L == R


def chain_ok(q, nu, pi):
    for i, s in enumerate(pi):
        A = pi[:i]
        if not (cycbal(q, A, s, s - 1) and cycbal(q, A, s, (nu + q - s) % q)):
            return False
    return True


def valid_seq(k, seq):
    S = set()
    for m in seq:
        r = min(m - 1, k - m)
        if sum(1 for x in range(m - r, m) if x in S) != sum(1 for x in range(m + 1, m + r + 1) if x in S):
            return False
        S.add(m)
    return True


def any_start(k, v0):
    """a valid k-strip sequence starting with v0 (claim (i) of live/PROOFS: parity blocks)."""
    if k == 0:
        return []
    if k == 1:
        return [1]
    c = v0 % 2                     # class of v0: odd (c = 1) or even
    n1 = (k + c) // 2
    first = [2 * y - c for y in any_start(n1, (v0 + c) // 2)]
    n2 = k - n1
    second = [2 * y - (1 - c) for y in any_start(n2, 1)]
    return first + second


def lemma_w(k, v0):
    """valid k-strip sequence starting with odd v0, v before 2v whenever 2v <= k."""
    if k == 0:
        return []
    odd = [2 * y - 1 for y in any_start((k + 1) // 2, (v0 + 1) // 2)]
    ev = [2 * y for y in (lemma_w(k // 2, 1) if k // 2 >= 1 else [])]
    return odd + ev


def build(q, t):
    M = q - 1
    k = M // 2
    z0 = t - 1
    if z0 % 4 == 2:                       # family (E)
        beta = lemma_w(k, z0 // 2)
        U = [2 * v for v in beta]
    elif (q - z0) % 4 == 2:               # family (O): z0 = q - 2 w0, w0 odd
        w0 = (q - z0) // 2
        gam = lemma_w(k, w0)
        U = [2 * (k + 1 - w) - 1 for w in gam]
    else:
        return None
    pi = [z + 1 for z in U] + [1] + [q + 1 - z for z in reversed(U)]
    return pi


if __name__ == '__main__':
    for q in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
        cov = []
        for t in range(2, q + 1):
            pi = build(q, t)
            if pi is None:
                continue
            assert sorted(pi) == list(range(1, q + 1)), (q, t, pi)
            if not (valid_seq(q, pi) and chain_ok(q, 1, pi) and pi[0] == t):
                print('FAIL', q, t, pi)
            else:
                cov.append(t)
        print(q, 'covered', cov, flush=True)
