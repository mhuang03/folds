"""trans.py: dilation-2 transversals of the sig-pairs of the q-strip (q odd), their
induced maps phi (sorted T), psi (sorted sig T), the induced residue nu' with
sig o phi = psi o sig_{k,nu'}, and the NotAgree (exceptional) pairs of phi, psi."""
import sys


def reach(n, t):
    return min(t - 1, n - t)


def sig(n, nu, t):
    return (nu - t) % n + 1


def agree(Q, k, phi, i, j):
    a, b = phi[i], phi[j]
    R = reach(Q, a)
    r = reach(k, i)
    l1 = (a - R <= b < a)
    l2 = (i - r <= j < i)
    r1 = (a < b <= a + R)
    r2 = (i < j <= i + r)
    return l1 == l2 and r1 == r2


def notagree(Q, k, phi):
    return [(i, j) for i in range(1, k + 1) for j in range(1, k + 1)
            if i != j and not agree(Q, k, phi, i, j)]


def fixpt(q, nu):
    return [t for t in range(1, q + 1) if sig(q, nu, t) == t][0]


def families(q, nu):
    """the 4 dilation-2 transversals (described by parities on the two reflection segments)."""
    k = (q - 1) // 2
    t0 = fixpt(q, nu)
    res = {}
    if nu % 2 == 1:
        # [1, nu]: same-parity pairs around t0: parity a below t0, 1-a above.
        # [nu+1, q]: opposite parity pairs: single parity b.
        for a in (0, 1):
            for b in (0, 1):
                T = [t for t in range(1, t0) if t % 2 == a] + \
                    [t for t in range(t0 + 1, nu + 1) if t % 2 != a] + \
                    [t for t in range(nu + 1, q + 1) if t % 2 == b]
                res[(a, b)] = T
    else:
        # [1, nu]: opposite parity pairs: single parity a;  [nu+1, q]: same parity around t0.
        for a in (0, 1):
            for b in (0, 1):
                T = [t for t in range(1, nu + 1) if t % 2 == a] + \
                    [t for t in range(nu + 1, t0) if t % 2 == b] + \
                    [t for t in range(t0 + 1, q + 1) if t % 2 != b]
                res[(a, b)] = T
    for key, T in res.items():
        assert len(T) == k, (q, nu, key, T)
        S = set(T) | {sig(q, nu, t) for t in T}
        assert len(S) == q - 1 and t0 not in S, (q, nu, key)
    return res


def analyse(q, nu, T):
    k = (q - 1) // 2
    phi = [None] + sorted(T)
    U = sorted(sig(q, nu, t) for t in T)
    psi = [None] + U
    inv = {v: i for i, v in enumerate(psi) if v is not None}
    # induced permutation  i -> psi^{-1}(sig(phi(i)))
    perm = [None] + [inv[sig(q, nu, phi[i])] for i in range(1, k + 1)]
    nus = [n2 for n2 in range(k) if all(perm[i] == sig(k, n2, i) for i in range(1, k + 1))]
    return phi, psi, perm, nus, notagree(q, k, phi), notagree(q, k, psi)


if __name__ == "__main__":
    q, nu = int(sys.argv[1]), int(sys.argv[2])
    for key, T in families(q, nu).items():
        phi, psi, perm, nus, e1, e2 = analyse(q, nu, T)
        print(key, "T=", T)
        print("   nu'=", nus, " #exc phi", len(e1), e1[:12], " #exc psi", len(e2), e2[:12])
