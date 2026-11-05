"""Summarise the SAT sweeps into a table: for each N, lower bound status (no valid sequence
with lg(N+1)-2 descents) and attainment status (a valid sequence with lg(N+1)-1 descents)."""
import re, os
lb, ub = {}, {}
def parse(fn, kind):
    if not os.path.exists(fn): return
    for l in open(fn):
        m = re.match(r'N=(\d+) k=(\d+) (.*)', l)
        if not m: continue
        N, k, rest = int(m[1]), int(m[2]), m[3]
        K = (N + 1).bit_length() - 1
        if kind == 'sweep':
            st = 'SAT' if rest.startswith('SAT') else 'UNSAT'
            (lb if k == K - 1 else ub)[N] = st
        else:
            ub[N] = 'SAT' if 'SAT(' in rest and ':SAT' in rest else ('UNSAT' if 'full:UNSAT' in rest else 'UNKNOWN')
parse('sat_sweep_1_55.txt', 'sweep'); parse('sat_lb_56_200.txt', 'sweep'); parse('sat_ub_1_120.txt', 'ub')
lbok = sorted(N for N, s in lb.items() if s == 'UNSAT')
print('lower bound (des >= lg(N+1)-1) verified for N =', f'{min(lbok)}..{max(lbok)}' if lbok else '-',
      ' all contiguous:', lbok == list(range(min(lbok), max(lbok) + 1)), ' failures:', [N for N, s in lb.items() if s != 'UNSAT'])
print('attained (des = lg(N+1)-1):', [N for N in sorted(ub) if ub[N] == 'SAT'][-1:], 'max N checked;',
      'NOT attained:', [N for N in sorted(ub) if ub[N] == 'UNSAT'], ' unknown:', [N for N in sorted(ub) if ub[N] == 'UNKNOWN'])
