#!/usr/bin/env python3
"""Independent checks against published formulas (data transcribed in the JSON files):
 (i)  Lepilov-O'Rourke-Swanson, Semigroup Forum 91 (2015): Theorems 3.1 (k=2) and 4.1 (k=3),
      compared with Rodseth's algorithm for all n <= NMAX covered by the theorems;
 (ii) Fel, arXiv:1608.08693, Section 4: matrices of minimal relations for k=4; for six values of
      the parameter in each of the 30 families we check that the rows are relations and that
      Fel's formula F = max(b11,b22) - (d1+d2+d3) agrees with Theorem 5.1 / Rodseth's algorithm.
Usage: python3 check_published.py [NMAX]"""
import json, sys, os
from fractions import Fraction as Fr
import sympy as sp
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from rod import rodseth_data
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
L = json.load(open(os.path.join(here, 'los_formulas.json')))
sq = {0: (lambda n: 2*n**3 - 5*n - 5, 16), 1: (lambda n: Fr(5, 2)*n**3 + Fr(1, 2)*n**2 - 6*n - 6, 9),
      2: (lambda n: 2*n**3 + 2*n**2 - n - 3, 6), 3: (lambda n: Fr(17, 4)*n**3 + Fr(9, 4)*n**2 - 8*n - 8, 7)}
cnt = bad = 0
for n in range(2, NMAX + 1):
    f, n0 = sq[n % 4]
    if n >= n0:
        cnt += 1; bad += f(n) != rodseth_data(n**2, (n+1)**2, (n+2)**2)['F']
print(f'(i) k=2: {cnt} values compared with [LOS15, Thm 3.1], disagreements: {bad}')
cnt = bad = 0
for n in range(2, NMAX + 1):
    r, m = n % 18, n // 18
    if m >= L['k3_m_min'][str(r)]:
        cnt += 1
        val = sum(c * m**e for e, c in enumerate(L['k3_f_coeffs_low_to_high'][str(r)]))
        bad += val != rodseth_data(n**3, (n+1)**3, (n+2)**3)['F']
print(f'(i) k=3: {cnt} values compared with [LOS15, Thm 4.1], disagreements: {bad}')
m = sp.symbols('m')
Fd = json.load(open(os.path.join(here, 'fel_k4_matrices.json')))
cnt = bad = 0
residues = set()
for fam in Fd['families']:
    E = [sp.sympify(e, locals={'m': m}) for e in fam['matrix']]
    for mm in range(max(fam['m_min'], 1), max(fam['m_min'], 1) + 6):
        N = fam['period'] * mm + fam['shift']; d = [(N - 1)**4, N**4, (N + 1)**4]
        residues.add((N - 1) % 40)
        A = [[int(e.subs(m, mm)) for e in E[3*i:3*i+3]] for i in range(3)]
        rel = all(sum(A[i][t] * d[t] for t in range(3)) == 0 for i in range(3))
        a11, a12, a13 = A[0][0], -A[0][1], -A[0][2]
        a21, a22, a23 = -A[1][0], A[1][1], -A[1][2]
        a31, a32, a33 = -A[2][0], -A[2][1], A[2][2]
        D0 = a11*a22*a33; D1 = a12*a23*a31; D2 = a13*a32*a21
        F = max(D0 + D1, D0 + D2) - sum(d)
        cnt += 1; bad += (not rel) or F != rodseth_data(*d)['F']
print(f'(ii) k=4: {len(Fd["families"])} families of [Fel16], {cnt} instances, residues of n mod 40 covered: '
      f'{len(residues)}, disagreements: {bad}')
