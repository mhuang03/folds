"""Check that every residue class mod q of the N-strip (any N, q need not divide N) is a
window-embedded copy of the |class|-strip: for x = phi(j), y = phi(i),
  phi(i) in left arm of phi(j)  <=>  i in left arm of j  (and the same for right arms)."""
import sys
def reach(n, m): return min(m - 1, n - m)
bad = 0
for N in range(1, int(sys.argv[1]) + 1):
    for q in range(1, N + 1):
        for s in range(1, q + 1):
            C = list(range(s, N + 1, q)); p = len(C)
            for j in range(1, p + 1):
                x = C[j - 1]; R = reach(N, x); r = reach(p, j)
                for i in range(1, p + 1):
                    y = C[i - 1]
                    if ((x - R <= y < x) != (j - r <= i < j)) or ((x < y <= x + R) != (j < i <= j + r)):
                        bad += 1
                        if bad < 5: print("fail", N, q, s, j, i)
print("failures:", bad)
