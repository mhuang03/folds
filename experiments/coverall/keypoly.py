"""keypoly.py: the key conditions of the edge certificates as cleared polynomials (sympy).

edge4 (f4-edge), family (K, L, R, al, be, s0, amin), w1 = (p, q), Delta = q(L+1) - pR:
  sigma8' = s0 - 1 - Kp/(L+1),  sigma9' = ((s0-1)(R+1) - Kq - 1)/R - 1,  sigma = sigma' - K/Delta
  chord(sigma) = (sigma(L+1) - 1 + Kp)(R+1) - ((sigma+1)R + 1 + Kq)L - L(R+1)
  bot(sigma)   = sigma - (L+1);  botR = sigma - (R+1);  amin(sigma) = sigma(L+1) + al - 1 - amin K
Each is A sigma + B; with sigma = n/den (den > 0) the cleared form is A n + B den.
"""
import sympy as sp

M, x, y, d, N, S = sp.symbols('M x y d N S')


def lin(expr, s):
    """expr linear in s: return (A, B)."""
    e = sp.expand(expr)
    A = e.coeff(s, 1)
    B = sp.expand(e - A * s)
    return A, B


def cleared(expr, s, sig):
    A, B = lin(expr, s)
    n, den = sp.fraction(sp.together(sig))
    return sp.factor(sp.expand(A * n + B * den)), den


def edge4(K, L, R, al, be, s0, amin, p, q):
    s = sp.Symbol('s')
    Dl = q * (L + 1) - p * R
    s8 = s0 - 1 - K * p / (L + 1)
    s9 = ((s0 - 1) * (R + 1) - K * q - 1) / R - 1
    conds = {
        'chord': (s * (L + 1) - 1 + K * p) * (R + 1) - ((s + 1) * R + 1 + K * q) * L - L * (R + 1),
        'bot': s - (L + 1),
        'botR': s - (R + 1),
        'amin': s * (L + 1) + al - 1 - amin * K,
    }
    out = {}
    for nm, sv in (('8', s8), ('9', s9)):
        sig = sp.together(sv - K / Dl)
        for cn, ce in conds.items():
            out[cn + nm] = cleared(ce, s, sig)
    return out


def edge1(K, L, R, al, be, s0, amin, p, q):
    t = sp.Symbol('t')
    Dl = p * (R + 1) - q * L
    t8 = ((s0 - 1) * (L + 1) - K * p - 1) / L - 1
    t9 = s0 - 1 - K * q / (R + 1)
    conds = {
        'chord': (t * (R + 1) - 1 + K * q) * (L + 1) - ((t + 1) * L + 1 + K * p) * R - R * (L + 1),
        'bot': t - (L + 1),
        'botR': t - (R + 1),
        'amin': (t + 1) * L + al - amin * K,
    }
    out = {}
    for nm, tv in (('8', t8), ('9', t9)):
        sig = sp.together(tv - K / Dl)
        for cn, ce in conds.items():
            out[cn + nm] = cleared(ce, t, sig)
    return out


def famZ(xx, yy):
    return (M, xx, yy, 0, 1, (M - 1) / sp.Integer(2), 2)


if __name__ == "__main__":
    for k, (P, den) in edge4(*famZ(y + d, y), 1, 1).items():
        print(k, '   den', den)
        print('   ', P)
