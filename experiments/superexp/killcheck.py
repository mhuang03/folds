"""Check the kill bound used in PROOFS.txt:  for inputs sigma = rev sigma', tau = rev tau'
(sigma', tau' in the slip family of size n, with top slip sets D', D''),
   G(sigma, tau)  contains  C_n minus at most 3|D'| + 3|D''| elements,
   C_n = odd k in [1, n-1] (n even),  odd k with 2k+1 <= n (n odd).
Only block membership matters, so we test random slip sets directly."""
import random
from family import good_set, modstar

def second_block(n, D):
    """Second block of a family member of size n with top slip set D (D empty for odd n)."""
    if n % 2:
        return set(range(1, n + 1, 2))
    h = n // 2
    d = [0] * (h + 2)
    for k in D:
        d[k] = 1
    return {2 * i - 1 - d[i - 1] for i in range(1, h + 1)}

def Cn(n):
    if n % 2 == 0:
        return {k for k in range(1, n) if k % 2}
    return {k for k in range(1, n) if k % 2 and 2 * k + 1 <= n}

rng = random.Random(5)
worst = 0
for trial in range(20000):
    n = rng.randint(2, 200)
    if n % 2:
        D1 = D2 = []
    else:
        h = n // 2
        D1 = [k for k in range(1, h) if rng.random() < rng.random()]
        D2 = [k for k in range(1, h) if rng.random() < rng.random()]
    S1, S2 = second_block(n, D1), second_block(n, D2)
    G = set(good_set(n, S1, S2))     # first(sigma) = S1 (second block of sigma'), first(tau) = S2
    C = Cn(n)
    missing = C - G
    assert len(missing) <= 3 * len(D1) + 3 * len(D2), (n, D1, D2, missing)
    worst = max(worst, len(missing) - 3 * (len(D1) + len(D2)))
    if not D1 and not D2:
        assert C <= G, (n, C - G)
print("kill bound holds in 20000 random trials; max(missing - 3(|D'|+|D''|)) =", worst)
