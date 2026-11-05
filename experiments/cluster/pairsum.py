"""Run ./kappa for N = 2..Nmax and store pair sums.  Output pairsum.txt:
N  y(N)=log(a/aW)  S1=sum kappa  S2=sum log(1+kappa)  [plus split by pair class]
Classes: LL (both left half), RR, LR (one each side), with middle panel counted as 'M'."""
import sys, os, subprocess, math
from wallis_exact import log_aW, A

HERE = os.path.dirname(os.path.abspath(__file__))

os.makedirs(os.path.join(HERE, "kdata"), exist_ok=True)


def kdata(N):
    fn = os.path.join(HERE, "kdata", "k%d.txt" % N)
    if not os.path.exists(fn):
        out = subprocess.check_output([os.path.join(HERE, "kappa"), str(N)]).decode()
        open(fn, "w").write(out)
    rows = []
    for line in open(fn):
        m, mp, r, rp, p, k = line.split()
        rows.append((int(m), int(mp), int(r), int(rp), float(p), float(k)))
    return rows


def side(N, m):
    if 2 * m == N + 1:
        return "M"
    return "L" if 2 * m < N + 1 else "R"


if __name__ == "__main__":
    Nmax = int(sys.argv[1])
    print("N    y        S1        S2      S2_LL     S2_LR    S2_M   y-S2")
    for N in range(3, Nmax + 1):
        S1 = S2 = 0.0
        cl = {"LL": 0.0, "LR": 0.0, "M": 0.0}
        for m, mp, r, rp, p, k in kdata(N):
            S1 += k
            l = math.log1p(k)
            S2 += l
            a, b = side(N, m), side(N, mp)
            if "M" in (a, b):
                cl["M"] += l
            elif a == b:
                cl["LL"] += l
            else:
                cl["LR"] += l
        y = math.log(A[N - 1]) - log_aW(N) if N <= len(A) else float("nan")
        print("%2d %8.4f %9.4f %9.4f %9.4f %9.4f %7.4f %8.4f" % (
            N, y, S1, S2, cl["LL"], cl["LR"], cl["M"], y - S2), flush=True)
