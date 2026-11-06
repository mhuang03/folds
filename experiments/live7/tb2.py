"""tb2.py u N1 N2 [step] [hmax]: two-sided Beatty copies with the EXACT slope N/p:
   TB'(N, p; h, h'; L) = {floor((iN - h)/p) : i <= L} + {N + 1 - floor((jN - h')/p) : j <= p - L}
with first element u and last element N + 1 - u; p odd != 7; inward window copies."""
import sys
sys.path.insert(0, '../live6')
from twoside import is_inward_copy


def tbx(N, p, h, h2, L):
    return [(i * N - h) // p for i in range(1, L + 1)] + \
        [N + 1 - (j * N - h2) // p for j in range(p - L, 0, -1)]


def sols(N, u, hmax=1, Lspread=None):
    out = []
    for p in range(3, N // 2 + 1, 2):
        if p == 7:
            continue
        for h in range(0, hmax + 1):
            if (N - h) // p != u:
                continue
            for h2 in range(0, hmax + 1):
                if (N - h2) // p != u:
                    continue
                Ls = range(1, p) if Lspread is None else range(max(1, p // 2 - Lspread), min(p, p // 2 + Lspread + 1))
                for L in Ls:
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
    for N in range(N1, N2 + 1, step):
        s = sols(N, u, hmax, 4)
        print(N, len(s), s[:10], flush=True)
