#!/usr/bin/env python3
"""Check that the closed forms used in the Lean formalization (lean/Frobenius/K4Phi.lean and
lean/Frobenius/K4GP.lean) are exactly the polynomials printed in the paper:
  phi_r  <->  Table A.3 (Frobenius number Φ_r),
  gam_r  <->  Table A.4 (genus),
  pfa_r, pfb_r <-> F_1, F_2 of (2.2) computed from Table A.1,
and that Table A.5 in lean/Frobenius/K4.lean is the paper's Table A.5.
Usage: python3 check_lean_vs_paper.py PAPER_TEX"""
import os, re, sys
import sympy as sp
here = os.path.dirname(os.path.abspath(__file__))
n, x = sp.symbols('n x')
tex = open(sys.argv[1], encoding='utf-8').read()

def table_rows(label):
    i = tex.index('\\label{' + label + '}'); j = tex.index('\\end{tabular}', i)
    body = tex[tex.index('\\midrule', i) + len('\\midrule'):j]
    return [r.strip() for r in body.split('\\\\') if '&' in r]

def parse_poly(s):
    s = s.strip().strip('$').replace('n^{', 'n**(').replace('}', ')')
    s = re.sub(r'(\d)n', r'\1*n', s)
    return sp.sympify(s, locals={'n': n})

def residues(cell):
    return [int(v) for v in cell.split(',')]

paper = {'phi': {}, 'gam': {}}
for lab, key in (('tab:F', 'phi'), ('tab:genus', 'gam')):
    for row in table_rows(lab):
        cells = [c.strip() for c in row.split('&')]
        for r in residues(cells[0]):
            paper[key][r] = sp.expand(parse_poly(cells[1]))
params = {}
for row in table_rows('tab:params'):
    cells = [c.strip() for c in row.split('&')]
    for r in residues(cells[0]):
        params[r] = [sp.expand(parse_poly(cl)) for cl in cells[1:5]]
a, b, c = n**4, (n + 1)**4, (n + 2)**4
lean = {}
for f in ('K4Phi.lean', 'K4GP.lean'):
    for m in re.finditer(r'def (phi|gam|pfa|pfb)(\d+) \(x : ℤ\) : ℤ := \((.*)\) / (\d+)', open(os.path.join(here, 'lean', 'Frobenius', f), encoding='utf-8').read()):
        lean[(m.group(1), int(m.group(2)))] = sp.expand(sp.sympify(m.group(3).replace('^', '**'), locals={'x': x}).subs(x, n) / int(m.group(4)))
bad = 0
for r in range(40):
    l, h, w, y = params[r]
    F1 = sp.expand((l - 1) * b + (h - y - 1) * c - a); F2 = sp.expand((l - w - 1) * b + (h - 1) * c - a)
    checks = [('phi', paper['phi'][r]), ('gam', paper['gam'][r]), ('pfa', F1), ('pfb', F2)]
    for key, ref in checks:
        if sp.expand(lean[(key, r)] - ref) != 0:
            bad += 1; print('MISMATCH', key, r)
    if sp.expand(paper['phi'][r] - F1) != 0 and sp.expand(paper['phi'][r] - F2) != 0:
        bad += 1; print('Phi is neither F1 nor F2 for r =', r)
# Table A.5
t5_paper = []
for row in table_rows('tab:exc'):
    cells = [cl.strip() for cl in row.split('&')]
    t5_paper.append((int(cells[0]), int(cells[1]), int(cells[2]), [int(v) for v in cells[3].split(',')]))
k4 = open(os.path.join(here, 'lean', 'Frobenius', 'K4.lean'), encoding='utf-8').read()
t5_lean = [(int(m.group(1)), int(m.group(2)), int(m.group(3)), [int(v) for v in m.group(4).split(',')])
           for m in re.finditer(r'\((\d+), (\d+), (\d+), \[([\d, ]+)\]\)', k4)]
if t5_lean != t5_paper:
    bad += 1; print('Table A.5 mismatch')
print(f'compared 4 x 40 closed forms and the {len(t5_paper)} rows of Table A.5: {bad} mismatches')
sys.exit(1 if bad else 0)
