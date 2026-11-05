"""General slip lemma, induced form, for ANY N and ANY first-block size n1 (n2 = N - n1).
kappa~(N a + r) = n1 a + kappa(r), lambda~(N a + r) = n2 a + lambda(r).
First block, permutation tau of [n1]: step j valid  <=>  t~(kappa~(2 f_j - 1)) = 2 t(j - 1)
   (t~ cyclic with modulus n1);
second block (all of X placed), permutation sigma of [n2]:
   step j valid  <=>  u~(lambda~(2 g_j - 1)) - 2 u(j - 1) = lambda~(2 g_j - 1) - (2j - 1)
   (u~ cyclic with modulus n2).
Exhaustive over all X and ALL permutations, N <= Nmax.  Usage: python3 gslipodd.py Nmax"""
import sys, itertools

def step_ok(p, placed, N):
    r = min(p - 1, N - p)
    return sum(placed[p - d] for d in range(1, r + 1)) == sum(placed[p + d] for d in range(1, r + 1))

def cyc(pl, y, m):
    a, r = divmod(y, m)
    return sum(pl[x] for x in range(1, r + 1)) + a * sum(pl[1:m + 1])

def main():
    Nmax = int(sys.argv[1])
    for N in range(2, Nmax + 1):
        bad = checks = 0
        for n1 in range(1, N):
            n2 = N - n1
            for X in itertools.combinations(range(1, N + 1), n1):
                Xs = set(X); f = [0] + list(X); g = [0] + [y for y in range(1, N + 1) if y not in Xs]
                kap = [0] * (N + 1)
                for y in range(1, N + 1): kap[y] = kap[y - 1] + (y in Xs)
                kt = lambda z: n1 * (z // N) + kap[z % N]
                lt = lambda z: z - kt(z)
                for t in itertools.permutations(range(1, n1 + 1)):
                    placed = [0] * (N + 2); pl = [0] * (n1 + 1)
                    for j in t:
                        v = step_ok(f[j], placed, N)
                        pr = cyc(pl, kt(2 * f[j] - 1), n1) == 2 * cyc(pl, j - 1, n1)
                        checks += 1; bad += v != pr
                        placed[f[j]] = 1; pl[j] = 1
                for sg in itertools.permutations(range(1, n2 + 1)):
                    placed = [0] * (N + 2); ul = [0] * (n2 + 1)
                    for x in X: placed[x] = 1
                    for j in sg:
                        v = step_ok(g[j], placed, N)
                        L = lt(2 * g[j] - 1)
                        pr = cyc(ul, L, n2) - 2 * cyc(ul, j - 1, n2) == L - (2 * j - 1)
                        checks += 1; bad += v != pr
                        placed[g[j]] = 1; ul[j] = 1
        print(f"N={N}: all n1, all X, all permutations: {checks} step checks, {bad} failures", flush=True)

if __name__ == '__main__':
    main()
