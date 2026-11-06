"""Generate the base block (M = 1, 18 <= K <= 36) of Folds/SymRun.lean.

For each K the five facts of `Body 1 K` are proved from
  * positive witnesses (an extendable prefix, checked by `goodB` = extB etc.), found by
    `symrun.bin wit`, and
  * negative facts `noLong K a d [] = true` (exhaustive pruned search),
using only the strongest facts and deriving the rest by `Good.mono'`.
phi(K) = G(K, K - floor(K/2)), psi(K) = G(K, K - ceil(K/2)).
Usage: python3 gen_base.py > base.lean.txt (then paste)."""
import subprocess

Gt = {}
out = subprocess.run(['./symrun.bin', 'base'], capture_output=True, text=True).stdout
for line in out.splitlines():
    if line.startswith('K='):
        k, rest = line.split(':')
        K = int(k[2:])
        for a, g in enumerate(map(int, rest.split()), 1):
            Gt[(K, K - a)] = g


def wit(K, L, d):
    s = subprocess.run(['./symrun.bin', 'wit', str(K), str(K - L), str(d)],
                       capture_output=True, text=True).stdout.strip()
    assert s.startswith('['), (K, L, d, s)
    return s


def Lof(form, K):
    return K // 2 if form == 'phi' else (K + 1) // 2


def Lexpr(form, K):
    return f'({K} / 2)' if form == 'phi' else f'(({K} + 1) / 2)'


def gen(K):
    phi, psi = Gt[(K, K // 2)], Gt[(K, (K + 1) // 2)]
    pos, neg, lines = [], [], []
    # positive witnesses
    if psi >= 6:
        pos.append(('psi', 6))
    else:
        if phi >= 6:
            pos.append(('phi', 6))
        if psi >= 5:
            pos.append(('psi', 5))
        else:
            if phi >= 5:
                pos.append(('phi', 5))
            pos.append(('psi', 4))
    # negative facts
    if phi == 4:
        neg.append(('phi', 5))
    elif phi == 5:
        neg.append(('phi', 6))
        if psi == 4:
            neg.append(('psi', 5))
    else:
        if psi == 5:
            neg.append(('psi', 6))
    for form, d in pos:
        lines.append(f'  have p_{form}{d} : Good {d} {K} {Lexpr(form, K)} :=\n'
                     f'    good_of_goodB (π := {wit(K, Lof(form, K), d)}) (by decide +kernel)')
    for form, d in neg:
        lines.append(f'  have n_{form}{d} : ¬ Good {d} {K} {Lexpr(form, K)} :=\n'
                     f'    not_good_of_noLong (by decide +kernel)')

    def prove(form, d):
        val = phi if form == 'phi' else psi
        if val >= d:
            for f2, d2 in pos:
                if d2 >= d and (f2 == 'psi' or form == 'phi'):
                    return f'(p_{f2}{d2}.mono\' rfl (by norm_num) (by norm_num))', True
            raise Exception((K, form, d))
        for f2, d2 in neg:
            if d2 <= d and (f2 == 'phi' or form == 'psi'):
                return f'(fun h => n_{f2}{d2} (h.mono\' rfl (by norm_num) (by norm_num)))', False
        raise Exception((K, form, d))

    t4, _ = prove('psi', 4)
    parts = [t4]
    for form, d in [('phi', 5), ('phi', 6), ('psi', 5), ('psi', 6)]:
        t, ok = prove(form, d)
        parts.append(f'iff_of_true {t} (by norm_num)' if ok else f'iff_of_false {t} (by norm_num)')
    body = '\n'.join(lines)
    return (f'theorem body_{K} : Body 1 {K} := by\n{body}\n'
            f'  exact ⟨{parts[0]},\n    ' + ',\n    '.join(parts[1:]) + '⟩\n')


for K in range(18, 37):
    print(gen(K))
