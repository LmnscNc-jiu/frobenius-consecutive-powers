#!/usr/bin/env python3
"""Generate the LaTeX bodies of Tables A.1-A.5 (k = 4) from the output of verify_k4.py, and optionally
check that the tables printed in the paper are exactly these.

verify_k4.py writes results_k4.json (the certificates of all forty classes, computed and checked in
exact arithmetic) and table3_k4.tex (the individually certified exceptional values n < 280).

Usage:  python3 verify_k4.py 20000          # writes results_k4.json, table3_k4.tex
        python3 make_tables_k4.py            # writes tab_params.tex, tab_Q.tex, tab_F.tex, tab_genus.tex
        python3 make_tables_k4.py --check ../manuscript/main.tex
"""
import json, re, sys
import sympy as sp

n = sp.symbols('n', integer=True)


def fmt(e):
    """(a_d n^d + ... + a_0)/den with integer coefficients, as printed in the paper"""
    num, den = sp.fraction(sp.together(sp.expand(e)))
    p = sp.Poly(sp.expand(num), n)
    terms = []
    for i in range(p.degree(), -1, -1):
        cf = p.coeff_monomial(n**i)
        if cf == 0:
            continue
        a = abs(cf)
        body = str(a) if i == 0 else ('' if a == 1 else str(a)) + ('n' if i == 1 else 'n^{%d}' % i)
        terms.append(('-' if cf < 0 else '+', body))
    out = ''.join(('' if j == 0 and s == '+' else s) + b for j, (s, b) in enumerate(terms))
    return '(%s)/%s' % (out, den) if den != 1 else out


def generate():
    R = json.load(open('results_k4.json'))
    R = {int(r): {k: (sp.sympify(v, locals={'n': n}) if k != 'big' else v) for k, v in d.items()}
         for r, d in R.items()}
    groups = {}
    for r in range(40):
        groups.setdefault(tuple(str(sp.expand(R[r][k])) for k in ('l', 'h', 'w', 'y')), []).append(r)
    rows = list(groups.values())
    out = {}
    out['tab:params'] = ''.join('%s & $%s$ & $%s$ & $%s$ & $%s$ \\\\\n' % (
        ', '.join(map(str, rs)), *(fmt(R[rs[0]][k]) for k in ('l', 'h', 'w', 'y'))) for rs in rows)
    out['tab:Q'] = ''.join('%s & $%s$ & $%s$ & %s & $F_{%s}$ & %s \\\\\n' % (
        ', '.join(map(str, rs)), fmt(R[rs[0]]['Q1']), fmt(R[rs[0]]['Q2']),
        ', '.join(str(int(R[r]['N'])) for r in rs), R[rs[0]]['big'][1],
        ', '.join(str(int(R[r]['Nbig'])) for r in rs)) for rs in rows)
    out['tab:F'] = ''.join('%s & $%s$ \\\\\n' % (', '.join(map(str, rs)), fmt(R[rs[0]]['Phi']))
                           for rs in rows)
    out['tab:genus'] = ''.join('%s & $%s$ \\\\\n' % (', '.join(map(str, rs)), fmt(R[rs[0]]['g']))
                               for rs in rows)
    out['tab:exc'] = open('table3_k4.tex').read()
    return out


def rows_of(body):
    return [re.sub(r'\s+', ' ', r).strip() for r in body.split('\\\\') if '&' in r]


def main():
    tables = generate()
    names = {'tab:params': 'tab_params.tex', 'tab:Q': 'tab_Q.tex', 'tab:F': 'tab_F.tex',
             'tab:genus': 'tab_genus.tex'}
    for lab, fn in names.items():
        open(fn, 'w').write(tables[lab])
    if len(sys.argv) > 2 and sys.argv[1] == '--check':
        tex = open(sys.argv[2], encoding='utf-8').read()
        for num, lab in enumerate(('tab:params', 'tab:Q', 'tab:F', 'tab:genus', 'tab:exc'), 1):
            i = tex.index('\\label{%s}' % lab); j = tex.index('\\end{tabular}', i)
            printed = rows_of(tex[tex.index('\\midrule', i) + len('\\midrule'):j].replace('\\bottomrule', ''))
            generated = rows_of(tables[lab])
            assert printed == generated, 'Table A.%d (%s) differs from the generated table' % (num, lab)
            print('Table A.%d (%s): %d rows, identical to the generated table' % (num, lab, len(printed)))
        print('ALL TABLES IDENTICAL')


if __name__ == '__main__':
    main()
