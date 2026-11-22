"""Generate the Lean files for Theorem 5.1 (k = 4) from the certificate data.
Usage: python3 gen_lean.py RESULTS_JSON OUTDIR [CLASSES]"""
import json, os, sys, sympy as sp
from fractions import Fraction
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from rod import rodseth_data

n, t = sp.symbols('n t')
R = json.load(open(sys.argv[1])); OUT = sys.argv[2]
classes = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else list(range(40))
a, b, c = n**4, (n + 1)**4, (n + 2)**4
EXC = [2, 4, 5, 6, 7, 8, 9, 12, 13, 16, 19, 20, 22, 23, 25, 26, 29, 32, 33, 39, 46, 59, 66, 79, 86,
       106, 119, 126, 146, 159, 166, 186, 199, 206, 239, 279]

def nat_poly(e, var='t'):
    p = sp.Poly(sp.expand(e), t)
    terms = []
    for (k,), cf in sorted(p.terms(), reverse=True):
        assert cf.is_integer and cf >= 0, (e, cf)
        if cf == 0: continue
        if k == 0: terms.append(str(cf))
        elif k == 1: terms.append(f'{cf} * {var}')
        else: terms.append(f'{cf} * {var} ^ {k}')
    return '(' + (' + '.join(terms) if terms else '0') + ')'

def int_poly_n(e):
    """integer polynomial in n as a Lean ℤ-expression in (n : ℤ)"""
    p = sp.Poly(sp.expand(e), n)
    s = ''
    for (k,), cf in sorted(p.terms(), reverse=True):
        assert cf.is_integer
        mon = '1' if k == 0 else ('(n : ℤ)' if k == 1 else f'(n : ℤ) ^ {k}')
        term = f'{abs(cf)}' if k == 0 else f'{abs(cf)} * {mon}'
        s += (' - ' if cf < 0 else (' + ' if s else '')) + term
    return s

def shift_for(r, d, big):
    m0 = 0
    while True:
        sub = {n: 40 * (t + m0) + r}
        L, H, W, Y, Q1, Q2, PH = [sp.expand(d[k].subs(sub)) for k in ('l', 'h', 'w', 'y', 'Q1', 'Q2', 'Phi')]
        U = sp.expand(L - W - 1); V = sp.expand(H - Y - 1)
        A, B, C = [sp.expand(x.subs(sub)) for x in (a, b, c)]
        F1 = sp.expand((L - 1) * B + (H - Y - 1) * C - A); F2 = sp.expand((L - W - 1) * B + (H - 1) * C - A)
        E = sp.expand(F1 - F2) if big == 'F1' else sp.expand(F2 - F1)
        def nn(x):
            return all(cc.is_integer and cc >= 0 for cc in sp.Poly(x, t).all_coeffs())
        ok = all(nn(x) for x in (W, Y, U, V, Q1, Q2, PH, E)) and sp.Poly(Q1, t).eval(0) > 0 \
            and sp.Poly(Q2, t).eval(0) > 0 and sp.expand(PH - (F1 if big == 'F1' else F2)) == 0
        if ok:
            return m0, dict(W=W, Y=Y, U=U, V=V, Q1=Q1, Q2=Q2, F=PH, E=E)
        m0 += 1

data = {}
for r in range(40):
    d = {k: sp.sympify(v, locals={'n': n}) for k, v in R[str(r)].items() if k in ('l', 'h', 'w', 'y', 'Q1', 'Q2', 'Phi')}
    data[r] = (d, R[str(r)]['big'])

# ---------- Phi ----------
def int_poly_x(e):
    p = sp.Poly(sp.expand(e), n)
    out = ''
    for (k,), cf in sorted(p.terms(), reverse=True):
        mon = '' if k == 0 else (' * x' if k == 1 else f' * x ^ {k}')
        term = f'{abs(cf)}{mon}'
        out += (' - ' if cf < 0 else (' + ' if out else '')) + term
    return out
lines = ['import Frobenius.Certificate', '', 'namespace FrobK4', '']
for r in range(40):
    num, den = sp.fraction(sp.together(data[r][0]['Phi']))
    lines.append(f'/-- `Φ_{{{r}}}` of Table A.3. -/')
    lines.append(f'def phi{r} (x : ℤ) : ℤ := ({int_poly_x(num)}) / {den}')
    lines.append('')
lines += ['/-- The closed form `Φ_r(n)` of Theorem 5.1 (Table A.3), `r = n mod 40`, as an integer-valued function. -/',
          'def Phi (n : ℕ) : ℤ :=', '  match n % 40 with']
for r in range(40):
    lines.append(f'  | {r} => phi{r} n')
lines += ['  | _ => 0', '', 'end FrobK4', '']
open(f'{OUT}/K4Phi.lean', 'w').write('\n'.join(lines))

# ---------- classes ----------
L = ['import Frobenius.Certificate', 'import Frobenius.K4Phi', '', 'namespace FrobK4', '', 'open FrobCert', '', 'set_option maxRecDepth 100000', '']
starts = {}
for r in classes:
    d, big = data[r]
    m0, P = shift_for(r, d, big)
    starts[r] = 40 * m0 + r
    N = f'(40 * (t + {m0}) + {r})'
    num, den = sp.fraction(sp.together(d['Phi']))
    W, Y, U, V, Q1, Q2, F, E = [nat_poly(P[k]) for k in ('W', 'Y', 'U', 'V', 'Q1', 'Q2', 'F', 'E')]
    a_ = f'{N} ^ 4'; b_ = f'({N} + 1) ^ 4'; c_ = f'({N} + 2) ^ 4'
    first = f'(({W} + {U}) * {b_} + {V} * {c_})'
    second = f'({U} * {b_} + ({Y} + {V}) * {c_})'
    if big == 'F1':
        maxlemma, small, bigx = 'max_eq_left', second, first
    else:
        maxlemma, small, bigx = 'max_eq_right', first, second
    L.append(f'''/-- Theorem 5.1, residue class `n ≡ {r} (mod 40)`, for `n ≥ {40*m0+r}`. -/
theorem class_{r} (t : ℕ) :
    ∃ F : ℕ, FrobeniusNumber F {{{a_}, {b_}, {c_}}} ∧ (F : ℤ) = Phi {N} := by
  refine ⟨{F}, ?_, ?_⟩
  · apply frob_uv (w := {W}) (y := {Y}) (u := {U}) (v := {V}) (q₁ := {Q1}) (q₂ := {Q2})
    · positivity
    · exact Nat.Coprime.pow 4 4 (by simp)
    · ring
    · ring
    · ring
    · positivity
    · positivity
    · rw [{maxlemma} (show {small} ≤ {bigx} from
        calc {small} ≤ {small} + {E} := Nat.le_add_right _ _
          _ = {bigx} := by ring)]
      ring
  · have hmod : {N} % 40 = {r} := by omega
    unfold Phi
    rw [hmod]
    unfold phi{r}
    exact Int.eq_ediv_of_mul_eq_right (by norm_num) (by push_cast; ring)
''')
L += ['end FrobK4', '']
open(f'{OUT}/K4Classes.lean', 'w').write('\n'.join(L))
json.dump(starts, open(f'{OUT}/starts.json', 'w'))
print('class starts', starts, 'max', max(starts.values()))
