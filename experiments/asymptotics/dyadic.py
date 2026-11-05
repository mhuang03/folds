"""Dyadic (binary-digit) decomposition of the validity defect for N = 2^L, on SMC snapshots.

Exact identity (NOTES.txt, section 2): with x = m - 1 = sum_i b_i 2^(L-i), S' = S - 1 (positions
0..N-1), n(w) = |S' in dyadic interval w|, w_i(x) = b_1..b_{i-1}0 and sigma = drop first digit,
    I(x) := P~(2m-1) - 2 P(m-1) = sum_{i=1}^{L} b_i(x) D(w_i(x)) + 1[S' contains 2x mod N],
    D(w) := n(sigma w) - 2 n(w).
m (free) is valid iff I(x) = 0.  This script checks the identity and measures, at t = k/N:
  * var over free x of each level term T_i(x) = b_i D(w_i(x)) and of I,
  * the share of var(I) from the diagonal (sum_i var T_i) vs cross-level covariances,
  * the Fourier spectrum: |S^(n)|^2 and the doubling-chain defect |S^(n/2) - S^(n)|^2 / (pi n)^2,
    summed in octaves n in [2^j, 2^(j+1)).
usage: python3 dyadic.py runs/dump_N.txt
"""
import sys
import numpy as np

fn = sys.argv[1]
lines = open(fn).read().split('\n')
snaps = {}
for ln in lines:
    if not ln.strip():
        continue
    a = list(map(int, ln.split()))
    snaps.setdefault(a[0], []).append(a[1:])
N = int(fn.split("dump_")[1].split("_")[0].split(".")[0])
L = N.bit_length() - 1
assert 1 << L == N

def analyse(k, frees):
    lev_var = np.zeros(L); tot = 0.0; checks = 0; spec_S = np.zeros(L + 1); spec_D = np.zeros(L + 1)
    covs = np.zeros((L, L)); nfree = 0
    for fr in frees:
        occ = np.ones(N, dtype=np.int64); occ[np.array(fr) - 1] = 0      # position p-1
        s = occ.sum()
        # direct I(x) for all x
        P = np.concatenate([[0], np.cumsum(occ)])                        # P[y] = #S' in [0,y)
        x = np.arange(N)
        y = 2 * x + 1
        Pt = np.where(y <= N, P[np.minimum(y, N)], s + P[np.maximum(y - N, 0)])
        I = Pt - 2 * P[x]
        # dyadic terms
        T = np.zeros((L, N), dtype=np.int64)
        for i in range(1, L + 1):
            bi = (x >> (L - i)) & 1
            # w_i = first i-1 digits of x then 0: interval start = (x >> (L-i+1)) << (L-i+1), length 2^(L-i)
            st = (x >> (L - i + 1)) << (L - i + 1); ln_ = 1 << (L - i)
            nw = P[st + ln_] - P[st]
            # sigma w_i = digits b_2..b_{i-1} 0 : interval of length 2^(L-i+1) starting at (st << 1) mod N
            st2 = (st << 1) % N; ln2 = ln_ << 1
            nsw = P[st2 + ln2] - P[st2]
            T[i - 1] = bi * (nsw - 2 * nw)
        loc = occ[(2 * x) % N]
        assert np.array_equal(T.sum(0) + loc, I), "identity fails"
        checks += 1
        free = occ == 0
        Tf = T[:, free].astype(float); If = I[free].astype(float)
        nfree += free.sum()
        Tc = Tf - Tf.mean(1, keepdims=True)
        covs += Tc @ Tc.T / free.sum()
        tot += If.var()
        # spectra
        Sh = np.fft.fft(occ - s / N)
        p = np.abs(Sh) ** 2
        n = np.arange(N)
        dd = np.zeros(N); dd[1:] = p[1:]
        ch = np.zeros(N)
        for nn in range(1, N // 2):
            prev = Sh[nn // 2] if nn % 2 == 0 else 0
            ch[nn] = abs(prev - Sh[nn]) ** 2 / (np.pi * nn) ** 2
        for j in range(L):
            lo, hi = 1 << j, min(1 << (j + 1), N // 2)
            if lo < hi:
                spec_S[j] += dd[lo:hi].sum() / (hi - lo); spec_D[j] += 2 * ch[lo:hi].sum()
    m = len(frees)
    covs /= m
    print(f"N={N} k={k} t={k / N:.3f} snapshots={m} identity checked on {checks}")
    print(f"  var I over free = {tot / m:.3f}   sum of level variances = {np.trace(covs):.3f}   "
          f"cross-level part = {covs.sum() - np.trace(covs):.3f}")
    print("  level variances var T_i (i = 1 coarse .. L fine):", " ".join(f"{v:.2f}" for v in np.diag(covs)))
    cr = covs / np.sqrt(np.outer(np.diag(covs), np.diag(covs)) + 1e-12)
    print("  corr(T_i, T_{i+1}):", " ".join(f"{cr[i, i + 1]:.2f}" for i in range(L - 1)))
    print("  mean |S^(n)|^2 / (N t(1-t)) per octave [2^j,2^j+1):", " ".join(f"{v / m / (N * (k / N) * (1 - k / N)):.3f}" for v in spec_S[:L - 1]))
    print("  var J from octave j (chain defects):", " ".join(f"{v / m:.3f}" for v in spec_D[:L - 1]))

for k in sorted(snaps):
    analyse(k, snaps[k])
