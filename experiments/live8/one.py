"""one.py N1 N2: check the explicit constructions for the pairs (1, v) (mirror (u', N),
u' = N + 1 - v, u' = N + 1 mod 2, 2 <= u' <= (N - 2)/2) in X(N, p, 0) with index a and the last
element N:
  u' = 2, 3: a = 1, p the largest odd number <= N/2 resp. <= N/3;
  A (4 <= u', 3u' <= N): a = max(2, ceil(u'(u'+1)/N)), p = floor(aN/u');
  B (3u' > N, g = N - 2u' >= 3): j = max(1, ceil(g(g-2)/N)), a = ceil(u'j/g), p = 2a + j;
  g = 2 (u' = (N-2)/2, N = 0 mod 4): chiY.
Conditions: floor(aN/p) = u', 2 <= a < p (or a = 1, p odd != 7), 2p <= N + 1."""
import sys


def ok(N, up, a, p):
    if p < 1 or 2 * p > N + 1 or a < 1 or a >= p:
        return False
    if a * N // p != up:
        return False
    if a == 1 and not (p % 2 == 1 and p != 7):
        return False
    return True


bad = 0
checked = 0
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for up in range(2, (N - 2) // 2 + 1):
        if (up - N - 1) % 2 != 0:
            continue
        g = N - 2 * up
        if up == 2:
            t = N // 2
            p = t if t % 2 == 1 else t - 1
            a = 1
        elif up == 3:
            t = N // 3
            p = t if t % 2 == 1 else t - 1
            a = 1
        elif 3 * up <= N:
            a = max(2, -(-up * (up + 1) // N))
            p = a * N // up
        elif g >= 3:
            j = max(1, -(-g * (g - 2) // N))
            a = -(-up * j // g)
            p = 2 * a + j
        else:
            assert g == 2 and N % 4 == 0  # chiY
            continue
        checked += 1
        if not ok(N, up, a, p):
            bad += 1
            if bad < 20:
                print('FAIL', N, up, 'g', g, 'a', a, 'p', p)
print("checked", checked, "bad", bad)
