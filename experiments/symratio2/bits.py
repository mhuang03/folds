"""bits.py -- the parity-bit structure of the head law t_m along a chain.

For m >= 19 a head window H = lift_a(H'), a = parity of its first entry (the TOP bit) and
H' a head at size floor/ceil(m/2) whose own top bit is p.  Prints the joint law of the first
few top bits (a_1 = top bit, a_2, ...) of the head of a uniform element of Theta(m), and the
2-bit transition table P(a_1 | a_2).
"""
import sys
import numpy as np
import wl


def bitstring(win, m, depth):
    """top `depth` bits of each window (all entries share them); value v -> (v + a) / 2."""
    v = win[:, 0].copy()
    out = []
    for _ in range(depth):
        a = v % 2
        out.append(a)
        v = (v + a) // 2
    return np.array(out).T


def main(m, depth):
    L = wl.law(m)
    t = L.t
    b = bitstring(L.win, m, depth)
    keys = b @ (1 << np.arange(depth))
    tab = np.bincount(keys, weights=t, minlength=1 << depth)
    print(f"m={m}: law of the top {depth} head bits (a_1 a_2 ...):")
    for k in range(1 << depth):
        s = "".join(str((k >> i) & 1) for i in range(depth))
        print("  ", s, f"{tab[k]:.6f}")
    p2 = np.bincount(b[:, 0] + 2 * b[:, 1], weights=t, minlength=4)
    print("  P(a1=a2) =", f"{p2[0] + p2[3]:.6f}", " P(a1!=a2) =", f"{p2[1] + p2[2]:.6f}")


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
