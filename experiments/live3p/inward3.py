# Check the closed form of Theorem G for 3-sets (PROOFS.txt section 2):
#   for a < b < c with 2b <= N+1, B = {a,b,c} satisfies the criterion of Theorem G
#   (for some centre) iff F(N,a,b,c); for 2b >= N+1 use the mirror image.
#   F = not(2a+2 <= b and c <= 2b-3) and not(c >= b+2 and 2c >= N+b+3 and (2a+2 <= b or 2b+2 <= N+a))
# Also checks that the three explicit centres 2a, 2b, 2c suffice (as in the Lean proof).
import sys

def imb(N, B, m):
    r = min(m - 1, N - m)
    return sum(1 for x in B if m - r <= x < m) - sum(1 for x in B if m < x <= m + r)

def inward_c2(N, B, c2):
    for m in range(1, N + 1):
        if m in B: continue
        if 2 * m == c2: return False
        I = imb(N, B, m)
        if 2 * m < c2 and I > 0: return False
        if 2 * m > c2 and I < 0: return False
    return True

def inward_any(N, B):
    neg = [m for m in range(1, N + 1) if m not in B and imb(N, B, m) < 0]
    pos = [m for m in range(1, N + 1) if m not in B and imb(N, B, m) > 0]
    return not neg or not pos or max(neg) < min(pos)

def F(N, a, b, c):
    return (not (2*a + 2 <= b and c <= 2*b - 3)) and \
        not (c >= b + 2 and 2*c >= N + b + 3 and (2*a + 2 <= b or 2*b + 2 <= N + a))

def Fsym(N, a, b, c):
    if 2 * b <= N + 1: return F(N, a, b, c)
    return F(N, N + 1 - c, N + 1 - b, N + 1 - a)

if __name__ == '__main__':
    bad = 0
    for N in range(3, int(sys.argv[1]) + 1):
        for a in range(1, N + 1):
            for b in range(a + 1, N + 1):
                for c in range(b + 1, N + 1):
                    B = {a, b, c}
                    g = inward_any(N, B)
                    if g != Fsym(N, a, b, c):
                        bad += 1; print("mismatch", N, a, b, c, g)
                    if 2 * b <= N + 1 and F(N, a, b, c):
                        n3 = c >= b + 2 and 2 * c >= N + b + 3
                        n2 = a + 2 <= b and c <= 2 * b - 3
                        c2 = 2 * c if n3 else (2 * b if n2 else 2 * a)
                        if not inward_c2(N, B, c2):
                            bad += 1; print("centre fails", N, a, b, c, c2)
    print("done, bad =", bad)
