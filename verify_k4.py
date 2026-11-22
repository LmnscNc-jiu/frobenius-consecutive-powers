#!/usr/bin/env python3
"""
Verification of Theorem 5.1 (the case k = 4) of the paper
  "On the Frobenius number of three consecutive k-th powers".

For S_n = <a,b,c> = <n^4, (n+1)^4, (n+2)^4> and each residue r = n mod 40 we are
given quadratic polynomials l_r, h_r, w_r, y_r (file table_k4.py).  Writing
n = 40 m + r, this script checks SYMBOLICALLY (exact rational arithmetic, sympy):

  (C1) l, h, w, y are integer-valued on Z (as polynomials in m);
  (C2) l*h - w*y = a                         (polynomial identity);
  (C3) l*b - y*c = a*Q1 and h*c - w*b = a*Q2 with Q1, Q2 in Q[n] integer-valued in m;
  (C4) Q1 > 0, Q2 > 0, w >= 0, y >= 1, l - w >= 1, h - y >= 1 for all m >= m0
       (thresholds computed exactly from isolating intervals of the real roots);

so that Lemma 2.1 of the paper applies for all n = 40m + r with m >= m0.  It then
prints F_1, F_2, the genus, the class threshold N_r, and which of F_1, F_2 is larger
from which point on.  Finally it

  * cross-checks the resulting closed form against Rodseth's algorithm for n <= NMAX,
  * certifies every remaining small n individually (Lemma 2.1 with numerical (l,h,w,y)),
  * writes LaTeX tables used in the paper.

Usage:  python3 verify_k4.py [NMAX]
"""
import sys, json
import sympy as sp
from table_k4 import TABLE
from rod import rodseth_data

M = 40
m, n = sp.symbols('m n', integer=True)
a, b, c = n**4, (n + 1)**4, (n + 2)**4


def poly_of(coeffs):
    return sum(sp.Rational(ci) * n**i for i, ci in enumerate(coeffs))


def integer_valued(expr_m):
    """A polynomial f in Q[m] is integer-valued on Z iff its Newton coefficients
    Delta^j f(0) (j = 0..deg f) are integers."""
    p = sp.Poly(sp.expand(expr_m), m)
    d = max(p.degree(), 0)
    vals = [p.eval(i) for i in range(d + 1)]
    for _ in range(d + 1):
        if not sp.Rational(vals[0]).q == 1:
            return False
        vals = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
    return True


def threshold(expr_m, strict=True):
    """Least m0 >= 0 such that expr(m) > 0 (resp. >= 0) for every integer m >= m0.
    Exact: uses rational isolating intervals of the real roots."""
    p = sp.Poly(sp.expand(expr_m), m, domain='QQ')
    ok = (lambda v: v > 0) if strict else (lambda v: v >= 0)
    if p.is_zero:
        if strict:
            raise ValueError('identically zero')
        return 0
    if p.degree() == 0:
        if ok(p.LC()):
            return 0
        raise ValueError('constant of wrong sign')
    if p.LC() < 0:
        raise ValueError('negative leading coefficient')
    ivs = p.intervals()
    U = max([iv[0][1] for iv in ivs], default=sp.Integer(-1))
    top = max(int(sp.ceiling(U)), 0)
    last_bad = -1
    for t in range(0, top + 1):
        if not ok(p.eval(t)):
            last_bad = t
    return last_bad + 1


def certificate_numeric(l, h, w, y, A, B, C):
    """Hypotheses of Lemma 2.1 for explicit integers."""
    return (l >= 1 and h >= 1 and 0 <= w < l and 0 <= y < h and l * h - w * y == A
            and (l * B - y * C) % A == 0 and (h * C - w * B) % A == 0
            and l * B > y * C and h * C > w * B)


def lemma_outputs(l, h, w, y, A, B, C):
    F1 = (l - 1) * B + (h - y - 1) * C - A
    F2 = (l - w - 1) * B + (h - 1) * C - A
    S = (h * B * l * (l - 1) + l * C * h * (h - 1)
         - (y * B * w * (2 * l - w - 1) + w * C * y * (2 * h - y - 1)))  # = 2 * sum of Apery set
    assert S % (2 * A) == 0 or (S - A * (A - 1)) % (2 * A) == 0
    twice_g = S // A - (A - 1)
    assert S % A == 0 and twice_g % 2 == 0
    g = twice_g // 2
    return F1, F2, g


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    results = {}
    for r in range(M):
        l, h, w, y = [poly_of(cf) for cf in TABLE[r]]
        sub = {n: M * m + r}
        Lm, Hm, Wm, Ym, Am = [sp.expand(t.subs(sub)) for t in (l, h, w, y, a)]
        # (C1)
        for t, nm in ((Lm, 'l'), (Hm, 'h'), (Wm, 'w'), (Ym, 'y')):
            assert integer_valued(t), (r, nm)
        # (C2)
        assert sp.expand(l * h - w * y - a) == 0, r
        # (C3)
        q1, r1 = sp.div(sp.Poly(sp.expand(l * b - y * c), n), sp.Poly(a, n))
        q2, r2 = sp.div(sp.Poly(sp.expand(h * c - w * b), n), sp.Poly(a, n))
        assert r1.is_zero and r2.is_zero, r
        Q1m = sp.expand(q1.as_expr().subs(sub)); Q2m = sp.expand(q2.as_expr().subs(sub))
        assert integer_valued(Q1m) and integer_valued(Q2m), r
        # (C4)
        th = dict(Q1=threshold(Q1m), Q2=threshold(Q2m), w=threshold(Wm, strict=False),
                  y=threshold(Ym), lw=threshold(Lm - Wm), hy=threshold(Hm - Ym),
                  wpos=threshold(Wm))
        m0 = max(th.values())
        F1 = sp.expand((l - 1) * b + (h - y - 1) * c - a)
        F2 = sp.expand((l - w - 1) * b + (h - 1) * c - a)
        D = sp.expand((F1 - F2).subs(sub))           # = w*b - y*c
        lc = sp.Poly(D, m).LC()
        big = 'F1' if lc > 0 else 'F2'
        mD = threshold(D if lc > 0 else -D)
        Ssum = (h * b * l * (l - 1) + l * c * h * (h - 1)
                - (y * b * w * (2 * l - w - 1) + w * c * y * (2 * h - y - 1))) / 2
        g = sp.expand(sp.cancel(Ssum / a) - (a - 1) / 2)
        Phi = F1 if big == 'F1' else F2
        other = F2 if big == 'F1' else F1
        results[r] = dict(l=l, h=h, w=w, y=y, Q1=q1.as_expr(), Q2=q2.as_expr(), m0=m0,
                          N=r + M * m0, big=big, Nbig=r + M * max(m0, mD), Phi=Phi,
                          other=other, g=g)
        print(f'r={r:2d}: certificate valid for n>={r + M*m0:4d}; max is {big} for n>={r + M*max(m0,mD):4d}')

    # --- closed form vs Rodseth, and individual certification of small n ---
    Nall = max(v['Nbig'] for v in results.values())
    print('closed form Phi_r(n) proved for all n >=', Nall, '(class by class thresholds above)')
    fails = []
    exceptional = []
    for N in range(1, NMAX + 1):
        r = N % M
        A, B, C = N**4, (N + 1)**4, (N + 2)**4
        d = rodseth_data(A, B, C)
        val = results[r]['Phi'].subs(n, N)
        if val != d['F']:
            fails.append(N)
        if N < results[r]['Nbig'] or val != d['F']:
            # certify individually with Lemma 2.1 (independent of Rodseth's theorem)
            l, h, w, y = d['sv'], d['pv1'], d['sv1'], d['pv']
            if N >= 2:
                assert certificate_numeric(l, h, w, y, A, B, C), N
                F1, F2, g = lemma_outputs(l, h, w, y, A, B, C)
                assert max(F1, F2) == d['F']
                pfs = sorted({F1, F2}) if (w >= 1 and y >= 1) else [max(F1, F2)]
                exceptional.append((N, max(F1, F2), g, pfs, val == d['F']))
    print('n <= %d where Phi_{n mod 40}(n) != F(S_n):' % NMAX, fails)
    assert all(x < Nall for x in fails)

    # --- LaTeX tables ---
    def tex_poly(e, var='n'):
        return sp.latex(sp.Poly(sp.expand(e), n).as_expr(), order='lex')

    rows = []
    seen = {}
    for r in range(M):
        key = tuple(str(results[r][k]) for k in ('l', 'h', 'w', 'y'))
        seen.setdefault(key, []).append(r)
    for key, rs in seen.items():
        R = results[rs[0]]
        rows.append((rs, R))
    with open('table1_k4.tex', 'w') as f:
        for rs, R in rows:
            f.write('%s & $%s$ & $%s$ & $%s$ & $%s$ & %d & $F_{%s}$ \\\\\n' % (
                ', '.join(map(str, rs)), tex_poly(R['l']), tex_poly(R['h']), tex_poly(R['w']),
                tex_poly(R['y']), min(results[x]['N'] for x in rs), R['big'][1]))
    with open('table2_k4.tex', 'w') as f:
        for rs, R in rows:
            Phi = sp.factor(R['Phi'])
            num, den = sp.fraction(sp.together(R['Phi']))
            f.write('%s & $\\frac{1}{%s}\\left(%s\\right)$ \\\\\n' % (
                ', '.join(map(str, rs)), sp.latex(den), sp.latex(sp.Poly(sp.expand(num), n).as_expr(), order='lex')))
    with open('table3_k4.tex', 'w') as f:
        for (N, F, g, pfs, agrees) in exceptional:
            if not agrees:
                f.write('%d & %d & %d & %s \\\\\n' % (N, F, g, ', '.join(map(str, pfs))))
    with open('table_genus_k4.tex', 'w') as f:
        for rs, R in rows:
            num, den = sp.fraction(sp.together(R['g']))
            f.write('%s & $\\frac{1}{%s}\\left(%s\\right)$ \\\\\n' % (
                ', '.join(map(str, rs)), sp.latex(den), sp.latex(sp.Poly(sp.expand(num), n).as_expr(), order='lex')))
    json.dump({r: {k: str(v) for k, v in R.items()} for r, R in results.items()},
              open('results_k4.json', 'w'), indent=1)
    lead = sorted(set(sp.Poly(R['Phi'], n).LC() for R in results.values()))
    print('leading coefficients of Phi_r:', lead)
    print('number of distinct parameter rows:', len(rows))
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    main()
