"""For N = 2^k: compare the cyclic 3-AP-free orderings of Z_N (panels 1..N <-> residues 0..N-1)
with the fully recursive parity-block semi-symmetric sequences (2^{N-1} of them)."""
from common import step_ok

def blocks(panels):
    """recursive parity-block orders of an arithmetic progression of panels."""
    if len(panels) == 1:
        return [list(panels)]
    ev, od = panels[1::2], panels[0::2]
    out = []
    for X in blocks(ev):
        for Y in blocks(od):
            out.append(X + Y); out.append(Y + X)
    return out

def semi_ok(seq, N):
    S = 0
    for m in seq:
        if not step_ok(S, m, N): return False
        S |= 1 << (m - 1)
    return True

def csym_ok(seq, N):
    S = set()
    for m in seq:
        x = m - 1
        for d in range(1, (N - 1) // 2 + 1):
            if (((x - d) % N) in S) != (((x + d) % N) in S): return False
        S.add(x)
    return True

def all_csym(N):
    res = []
    def rec(seq, used):
        if len(seq) == N: res.append(tuple(seq)); return
        for m in range(1, N + 1):
            if m not in used and csym_ok(seq + [m], N):
                rec(seq + [m], used | {m})
    rec([], set())
    return res

for N in (2, 4, 8, 16):
    B = set(tuple(b) for b in blocks(list(range(1, N + 1))))
    assert all(semi_ok(b, N) for b in B)
    out = f"N={N}: |blocks|={len(B)}"
    if N <= 8:
        C = set(all_csym(N))
        out += f" |csym|={len(C)} equal={B == C}"
        out += f" csym all semi-valid={all(semi_ok(c, N) for c in C)}"
    else:
        out += f" blocks all csym={all(csym_ok(list(b), N) for b in B)}"
    print(out)
for N in range(3, 14):
    B = blocks(list(range(1, N + 1)))
    print(N, len(B), len(set(map(tuple, B))), all(semi_ok(b, N) for b in B))
