"""Causal test of the mod-3 mechanism: remove the constraints of the four panels at the
doubling 2-cycle {j, j+1, N-j, N+1-j}, j = floor((N+1)/3) (for N = 3k these are k, k+1, 2k, 2k+1),
or, as a control, four panels around N/4 (j = floor((N+1)/4)) or N/5, and test whether
the [3|N] excess survives in
    y_T(N) = log a_{-T}(N) - [ log a_W(N) - sum_{m in T} log w(r_m) ].
Writes knockout.txt: N label y_T."""
import sys, os, subprocess, math
import numpy as np
from wallis_exact import log_aW, logw, A

HERE = os.path.dirname(os.path.abspath(__file__))
fn = os.path.join(HERE, "knockout.txt")


def T(N, d):
    j = (N + 1) // d
    return sorted({j, j + 1, N - j, N + 1 - j})


def yT(N, d):
    t = T(N, d)
    c = int(subprocess.check_output([os.path.join(HERE, "dpx"), str(N)] + [str(p) for p in t]))
    return math.log(c) - (log_aW(N) - sum(logw(min(m - 1, N - m)) for m in t))


if __name__ == "__main__" and sys.argv[1] != "fit":
    N0, N1 = int(sys.argv[1]), int(sys.argv[2])
    with open(fn, "a") as f:
        for N in range(N0, N1 + 1):
            for d in (3, 4, 5):
                f.write("%d %d %.10f\n" % (N, d, yT(N, d)))
                f.flush()

if __name__ == "__main__" and sys.argv[1] == "fit":
    data = {}
    for line in open(fn):
        N, d, v = line.split()
        data[(int(N), int(d))] = float(v)
    for label, get in [("full y", lambda N: math.log(A[N - 1]) - log_aW(N))] + \
            [("knockout d=%d" % d, (lambda d: lambda N: data[(N, d)])(d)) for d in (3, 4, 5)]:
        for Nmin in (10, 12):
            Ns = [N for N in range(Nmin, 34) if (N, 3) in data]
            X = np.array([[N % 2 == 0, N % 2 == 1, (N % 2 == 0) * N / 30, (N % 2 == 1) * N / 30,
                           (N % 2 == 0) * (N / 30) ** 2, (N % 2 == 1) * (N / 30) ** 2,
                           (N % 2 == 0) * (N / 30) ** 3, (N % 2 == 1) * (N / 30) ** 3, N % 3 == 0]
                          for N in Ns], float)
            yv = np.array([get(N) for N in Ns])
            b, *_ = np.linalg.lstsq(X, yv, rcond=None)
            r = yv - X @ b
            s2 = r @ r / (len(Ns) - X.shape[1])
            se = math.sqrt(s2 * np.linalg.inv(X.T @ X)[-1, -1])
            print("%-14s N=%d..%d  delta3 = %+.4f (%.4f)   rms=%.4f" % (label, Nmin, Ns[-1], b[-1], se, math.sqrt(s2)))
