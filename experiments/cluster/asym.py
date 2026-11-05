"""Asymptotic fits for log a(N).

log a(N) = log a_W(N) + y(N),   log a_W(N) = (N/2) log(pi N/(2e)) + (1/4) log N + gW + 1/(6N) + O(N^-2),
gW = (1/3) log 2 + (1/2) log pi + 3 zeta'(-1)  (exact, wallis_exact.py).
We fit y(N) with several ansaetze, all with a parity constant and the [3|N] indicator."""
import math
import numpy as np
from wallis_exact import log_aW, A

Ns = np.arange(1, len(A) + 1)
y = np.array([math.log(A[N - 1]) - log_aW(N) for N in Ns])
logA = np.array([math.log(a) for a in A])

forms = {
    "aN+b logN":            lambda N: [N, np.log(N)],
    "aN+bN^2":              lambda N: [N, N ** 2 / 30.0],
    "c NlogN + aN":         lambda N: [N * np.log(N), N],
    "c NlogN + aN + b logN": lambda N: [N * np.log(N), N, np.log(N)],
    "aN + b N^1.5":         lambda N: [N, N ** 1.5 / 10],
    "-N loglogN + aN":       lambda N: [N * np.log(np.log(N)), N],
}


def design(f, Ns_sel):
    N = Ns_sel.astype(float)
    cols = f(N) + [(Ns_sel % 2 == 0).astype(float), (Ns_sel % 2 == 1).astype(float), (Ns_sel % 3 == 0).astype(float)]
    return np.array(cols).T


if __name__ == "__main__":
    for Nmin in (10, 14, 18):
        print("fits of y(N) on N >= %d (plus even/odd constants and [3|N]):" % Nmin)
        Ns_sel = Ns[Ns >= Nmin]
        for name, f in forms.items():
            X = design(f, Ns_sel)
            b, *_ = np.linalg.lstsq(X, y[Ns >= Nmin], rcond=None)
            r = y[Ns >= Nmin] - X @ b
            # out-of-sample: fit on N<=29, predict 30..33
            m = Ns_sel <= 29
            b2, *_ = np.linalg.lstsq(X[m], y[Ns >= Nmin][m], rcond=None)
            pr = y[Ns >= Nmin][~m] - X[~m] @ b2
            print("  %-24s rms=%.4f  coef=%s  pred.err(30..33)=%s" % (
                name, math.sqrt(np.mean(r ** 2)), np.round(b, 4), np.round(pr, 3)))
    # local slope: effective coefficient of N log N in log a(N), from 3-point local fits per parity
    print("\nlocal effective N log N coefficient of log a(N): fit log a = c N log N + a N + b over N-4, N-2, N, N+2, N+4")
    for N in range(9, 30):
        idx = [N - 4, N - 2, N, N + 2, N + 4]
        X = np.array([[n * math.log(n), n, 1.0] for n in idx])
        b, *_ = np.linalg.lstsq(X, np.array([logA[n - 1] for n in idx]), rcond=None)
        print("  N=%2d c=%.3f" % (N, b[0]))
