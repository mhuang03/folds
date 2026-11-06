"""tb3.py u N1 N2 [step] [hmax] [Lspread]: two-sided Beatty copies with slope (N+1)/(p+1):
   TB''(N, p; e, e'; L) = {floor((i(N+1) - e)/(p+1)) : i <= L}
                        + {N + 1 - floor((j(N+1) - e')/(p+1)) : j <= p - L}
first element u, last N + 1 - u, p odd != 7, inward window copies."""
import sys
sys.path.insert(0, '../live6')
from twoside import is_inward_copy


def tbx(N, p, h, h2, L):
    M, q = N + 1, p + 1
    return [(i * M - h) // q for i in range(1, L + 1)] + \
        [M - (j * M - h2) // q for j in range(p - L, 0, -1)]


def sols(N, u, hmax=1, Lspread=4, odd=True):
    out = []
    for p in range(3, N // 2 + 1, 2 if odd else 1):
        if p == 7 and odd:
            continue
        for h in range(0, hmax + 1):
            if (N + 1 - h) // (p + 1) != u:
                continue
            for h2 in range(0, hmax + 1):
                if (N + 1 - h2) // (p + 1) != u:
                    continue
                for L in range(max(1, p // 2 - Lspread), min(p, p // 2 + Lspread + 1)):
                    X = tbx(N, p, h, h2, L)
                    if any(X[i] >= X[i + 1] for i in range(len(X) - 1)):
                        continue
                    if is_inward_copy(N, X):
                        out.append((p, h, h2, L, p - L))
    return out


if __name__ == '__main__':
    u, N1, N2 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    step = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    hmax = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    Ls = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    for N in range(N1, N2 + 1, step):
        s = sols(N, u, hmax, Ls)
        print(N, len(s), s[:10], flush=True)
