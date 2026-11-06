"""Shared data loaders for experiments/structure2."""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..')


def counts():
    """a(N) (semi) and s(N) (symmetric, A003407) from experiments/semi_counts.txt."""
    a, s = {}, {}
    for line in open(os.path.join(ROOT, 'experiments', 'semi_counts.txt')):
        if line.startswith('#') or not line.strip():
            continue
        p = line.split()
        a[int(p[0])] = int(p[1])
        if len(p) > 2 and p[2] not in ('-', '?'):
            try:
                s[int(p[0])] = int(p[2])
            except ValueError:
                pass
    return a, s


def selfdual():
    """c(N), N = 1..41, from experiments/arith/selfdual_out.txt (+ selfdual2_out.txt)."""
    c = {}
    for fn in ('selfdual_out.txt', 'selfdual2_out.txt'):
        p = os.path.join(ROOT, 'experiments', 'arith', fn)
        if not os.path.exists(p):
            continue
        for line in open(p):
            p = line.split()
            if len(p) == 2 and p[0].isdigit() and p[1].isdigit():
                c[int(p[0])] = int(p[1])
    return c


def stats(n, rule='semi'):
    """Parse `folds stats` output.  Returns dict with total, prefixes, reach, dead,
    alive, doomed, F (by_first, m = 1..N), F2 (rows m, cols x)."""
    cands = [os.path.join(HERE, 'data', f'stats_{n}.txt') if rule == 'semi'
             else os.path.join(HERE, 'data', f'{rule}stats_{n}.txt'),
             os.path.join(ROOT, 'rust', 'results', 'stats', f'{rule}_{n}.txt')]
    fn = next(p for p in cands if os.path.exists(p) and os.path.getsize(p) > 0)
    d = {'F2': []}
    lines = open(fn).read().split('\n')
    for i, line in enumerate(lines):
        if line.startswith('total'):
            d['total'] = int(line.split()[1])
        for key, tag in (('prefixes', 'prefixes('), ('reach', 'reachable_sets('),
                         ('dead', 'dead_end_sets('), ('alive', 'alive_sets('),
                         ('doomed', 'doomed_sets('), ('F', 'by_first=')):
            if line.startswith(tag):
                d[key] = [int(x) for x in line.split()[1:]]
        if line.startswith('by_first2'):
            d['F2'] = [[int(x) for x in lines[i + 1 + r].split()] for r in range(n)]
    return d
