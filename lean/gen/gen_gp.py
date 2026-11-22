"""Generate the genus / pseudo-Frobenius parts of the k = 4 formalization:
  Frobenius/K4GP.lean       : gam_r, pfa_r, pfb_r and Gam, PFa, PFb (Tables A.3-A.4, both PF numbers)
  Frobenius/K4ClassesGP.lean: for each class r, genus and PF set for n >= start_r
  Frobenius/K4Small.lean    : numerical certificates (F, genus, PF) for 2 <= n <= NMAX
Usage: python3 gen_gp.py RESULTS_JSON STARTS_JSON EXC_JSON OUTDIR NMAX"""
import json, os, sys
import sympy as sp
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '..', '..'))

from rod import rodseth_data

n, t = sp.symbols('n t')
R = json.load(open(sys.argv[1])); starts = json.load(open(sys.argv[2]))
EXC = json.load(open(sys.argv[3])); OUT = sys.argv[4]; NMAX = int(sys.argv[5])
a, b, c = n**4, (n + 1)**4, (n + 2)**4
FEXC = [2, 4, 5, 6, 7, 8, 9, 12, 13, 16, 19, 20, 22, 23, 25, 26, 29, 32, 33, 39, 46, 59, 66, 79, 86,
        106, 119, 126, 146, 159, 166, 186, 199, 206, 239, 279]

def nat_poly(e):
    p = sp.Poly(sp.expand(e), t); terms = []
    for (k,), cf in sorted(p.terms(), reverse=True):
        assert cf.is_integer and cf >= 0, (e, cf)
        terms.append(str(cf) if k == 0 else (f'{cf} * t' if k == 1 else f'{cf} * t ^ {k}'))
    return '(' + (' + '.join(terms) if terms else '0') + ')'

def int_poly_x(e):
    p = sp.Poly(sp.expand(e), n); out = ''
    for (k,), cf in sorted(p.terms(), reverse=True):
        mon = '' if k == 0 else (' * x' if k == 1 else f' * x ^ {k}')
        out += (' - ' if cf < 0 else (' + ' if out else '')) + f'{abs(cf)}{mon}'
    return out

D = {}
for r in range(40):
    d = {k: sp.sympify(v, locals={'n': n}) for k, v in R[str(r)].items() if k in ('l', 'h', 'w', 'y', 'Q1', 'Q2', 'g')}
    d['P1'] = sp.expand((d['l'] - 1) * b + (d['h'] - d['y'] - 1) * c - a)
    d['P2'] = sp.expand((d['l'] - d['w'] - 1) * b + (d['h'] - 1) * c - a)
    D[r] = d

# ---- K4GP.lean ----
L = ['import Frobenius.K4Phi', '', 'namespace FrobK4', '']
for nm, key in (('gam', 'g'), ('pfa', 'P1'), ('pfb', 'P2')):
    for r in range(40):
        num, den = sp.fraction(sp.together(D[r][key]))
        L.append(f'def {nm}{r} (x : ℤ) : ℤ := ({int_poly_x(num)}) / {den}')
    L.append('')
for nm, Nm, doc in (('gam', 'Gam', 'the genus (Table A.4)'),
                    ('pfa', 'PFa', 'the pseudo-Frobenius number `F₁ = (l-1)b + (h-y-1)c - a`'),
                    ('pfb', 'PFb', 'the pseudo-Frobenius number `F₂ = (l-w-1)b + (h-1)c - a`')):
    L += [f'/-- Closed form of {doc} on the residue class `n mod 40`. -/', f'def {Nm} (n : ℕ) : ℤ :=',
          '  match n % 40 with'] + [f'  | {r} => {nm}{r} n' for r in range(40)] + ['  | _ => 0', '']
for Nm, nm in (('Gam', 'gam'), ('PFa', 'pfa'), ('PFb', 'pfb')):
    for r in range(40):
        L += [f'theorem {Nm}_eq_{r} (n : ℕ) (h : n % 40 = {r}) : {Nm} n = {nm}{r} n := by',
              f'  simp only [{Nm}, h]', '']
L += ['end FrobK4', '']
open(f'{OUT}/K4GP.lean', 'w').write('\n'.join(L))

# ---- K4ClassesGP.lean ----
L = ['import Frobenius.Apery', 'import Frobenius.K4GP', 'import Frobenius.K4Classes  -- only to serialize the two heavy builds', '', 'namespace FrobK4', '', 'open FrobCert', '',
     'set_option maxRecDepth 100000', '']
for r in range(40):
    d = D[r]; m0 = (starts[str(r)] - r) // 40
    sub = {n: 40 * (t + m0) + r}
    Lx, Hx, Wx, Yx, Q1, Q2, G, P1, P2 = [sp.expand(d[k].subs(sub)) for k in ('l', 'h', 'w', 'y', 'Q1', 'Q2', 'g', 'P1', 'P2')]
    Ux = sp.expand(Lx - Wx - 1); Vx = sp.expand(Hx - Yx - 1)
    assert sp.Poly(Wx, t).eval(0) >= 1 and sp.Poly(Yx, t).eval(0) >= 1
    W, Y, U, V, q1, q2, Gs, p1, p2 = [nat_poly(x) for x in (Wx, Yx, Ux, Vx, Q1, Q2, G, P1, P2)]
    N = f'(40 * (t + {m0}) + {r})'
    A = f'{N} ^ 4'; B = f'({N} + 1) ^ 4'; Cc = f'({N} + 2) ^ 4'
    gnum, gden = sp.fraction(sp.together(d['g']))
    adn = sp.fraction(sp.together(d['P1']))[1]; bdn = sp.fraction(sp.together(d['P2']))[1]
    L.append(f'''/-- Genus, pseudo-Frobenius numbers and type for `n ≡ {r} (mod 40)`, `n ≥ {40*m0+r}`. -/
theorem classGP_{r} (t : ℕ) :
    (genus {{{A}, {B}, {Cc}}} : ℤ) = Gam {N} ∧
    (∀ x : ℕ, IsPF {{{A}, {B}, {Cc}}} x ↔ ((x : ℤ) = PFa {N} ∨ (x : ℤ) = PFb {N})) ∧
    Set.ncard {{x | IsPF {{{A}, {B}, {Cc}}} x}} = 2 := by
  have C : Cert ({A}) ({B}) ({Cc}) ({W} + {U} + 1) ({Y} + {V} + 1) {W} {Y} {q1} {q2} :=
    ⟨by positivity, Nat.Coprime.pow 4 4 (by simp), by omega, by omega, by ring, by ring, by ring,
      by positivity, by positivity⟩
  have hb : 0 < {B} := by positivity
  have hc : 0 < {Cc} := by positivity
  have hw1 : 1 ≤ {W} := Nat.succ_le_of_lt (by positivity)
  have hy1 : 1 ≤ {Y} := Nat.succ_le_of_lt (by positivity)
  have h1 : {p1} + {A} = ({W} + {U}) * {B} + {V} * {Cc} := by ring
  have h2 : {p2} + {A} = {U} * {B} + ({Y} + {V}) * {Cc} := by ring
  have hmod : {N} % 40 = {r} := by omega
  refine ⟨?_, ?_, type_uv C hb hc hw1 hy1 h1 h2⟩
  · have hg := genus_uv C
    have hR : {Gs} * {A} * 2 + {A} * {A} + {W} * {Y} * (({W} + 2 * {U} + 1) * {B} + ({Y} + 2 * {V} + 1) * {Cc})
        = ({W} + {U} + 1) * ({Y} + {V} + 1) * (({W} + {U}) * {B} + ({Y} + {V}) * {Cc}) + {A} := by ring
    have hG : genus {{{A}, {B}, {Cc}}} = {Gs} := by
      have hpos : 0 < {A} * 2 := by positivity
      apply Nat.eq_of_mul_eq_mul_right hpos
      have e1 : genus {{{A}, {B}, {Cc}}} * ({A} * 2) = genus {{{A}, {B}, {Cc}}} * {A} * 2 := by ring
      have e2 : {Gs} * ({A} * 2) = {Gs} * {A} * 2 := by ring
      rw [e1, e2]; omega
    rw [hG, Gam_eq_{r} _ hmod]; unfold gam{r}
    exact Int.eq_ediv_of_mul_eq_right (by norm_num) (by push_cast; ring)
  · intro x
    rw [pf_uv C hb hc hw1 hy1 h1 h2 x]
    have e1 : (({p1} : ℕ) : ℤ) = PFa {N} := by
      rw [PFa_eq_{r} _ hmod]; unfold pfa{r}
      exact Int.eq_ediv_of_mul_eq_right (by norm_num) (by push_cast; ring)
    have e2 : (({p2} : ℕ) : ℤ) = PFb {N} := by
      rw [PFb_eq_{r} _ hmod]; unfold pfb{r}
      exact Int.eq_ediv_of_mul_eq_right (by norm_num) (by push_cast; ring)
    rw [← e1, ← e2]
    constructor
    · rintro (h | h) <;> [left; right] <;> exact_mod_cast h
    · rintro (h | h) <;> [left; right] <;> exact_mod_cast h
''')
L += ['end FrobK4', '']
open(f'{OUT}/K4ClassesGP.lean', 'w').write('\n'.join(L))

# ---- K4Small.lean ----
rows = []
for N in range(2, NMAX + 1):
    A_, B_, C_ = N**4, (N + 1)**4, (N + 2)**4
    dd = rodseth_data(A_, B_, C_); l, h, w, y = dd['sv'], dd['pv1'], dd['sv1'], dd['pv']
    q1, r1 = divmod(l * B_ - y * C_, A_); q2, r2 = divmod(h * C_ - w * B_, A_)
    assert r1 == 0 and r2 == 0 and q1 > 0 and q2 > 0 and w < l and y < h and l * h - w * y == A_
    u, v = l - w - 1, h - y - 1
    F = max((w + u) * B_ + v * C_, u * B_ + (y + v) * C_) - A_
    S2 = l * h * ((l - 1) * B_ + (h - 1) * C_) - w * y * ((2 * l - w - 1) * B_ + (2 * h - y - 1) * C_)
    g = (S2 - A_ * (A_ - 1)) // (2 * A_)
    if w >= 1 and y >= 1:
        p1 = (w + u) * B_ + v * C_ - A_; p2 = u * B_ + (y + v) * C_ - A_
    else:
        p1 = p2 = (w + u) * B_ + (y + v) * C_ - A_
    rows.append((N, w, y, u, v, q1, q2, F, g, p1, p2))
L = ['import Frobenius.Apery', 'import Frobenius.K4Phi', 'import Frobenius.K4GP', '', 'namespace FrobK4', '',
     'open FrobCert', '', 'set_option maxRecDepth 100000', '',
     '/-- A numerical certificate for `S_n = ⟨n^4, (n+1)^4, (n+2)^4⟩`: the parameters of `frob_uv`',
     'together with the claimed Frobenius number `F`, genus `g` and pseudo-Frobenius numbers `p₁, p₂`. -/',
     'structure NCert where', '  n : ℕ', '  w : ℕ', '  y : ℕ', '  u : ℕ', '  v : ℕ', '  q₁ : ℕ', '  q₂ : ℕ',
     '  F : ℕ', '  g : ℕ', '  p₁ : ℕ', '  p₂ : ℕ', '  deriving DecidableEq', '',
     '/-- The certificate hypotheses (Boolean form). -/',
     'def NCert.okC (c : NCert) : Bool :=',
     '  0 < c.n ^ 4 && Nat.gcd (c.n ^ 4) ((c.n + 1) ^ 4) == 1 &&',
     '  (c.w + c.u + 1) * (c.y + c.v + 1) == c.n ^ 4 + c.w * c.y &&',
     '  c.y * (c.n + 2) ^ 4 + c.n ^ 4 * c.q₁ == (c.w + c.u + 1) * (c.n + 1) ^ 4 &&',
     '  c.w * (c.n + 1) ^ 4 + c.n ^ 4 * c.q₂ == (c.y + c.v + 1) * (c.n + 2) ^ 4 &&',
     '  0 < c.q₁ && 0 < c.q₂', '',
     '/-- The full check: certificate, Frobenius number, genus and pseudo-Frobenius numbers. -/',
     'def NCert.ok (c : NCert) : Bool :=',
     '  c.okC &&',
     '  c.F + c.n ^ 4 == max ((c.w + c.u) * (c.n + 1) ^ 4 + c.v * (c.n + 2) ^ 4)',
     '    (c.u * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4) &&',
     '  c.g * c.n ^ 4 * 2 + c.n ^ 4 * c.n ^ 4 +',
     '      c.w * c.y * ((c.w + 2 * c.u + 1) * (c.n + 1) ^ 4 + (c.y + 2 * c.v + 1) * (c.n + 2) ^ 4) ==',
     '    (c.w + c.u + 1) * (c.y + c.v + 1) * ((c.w + c.u) * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4)',
     '      + c.n ^ 4 &&',
     '  ((decide (1 ≤ c.w ∧ 1 ≤ c.y) &&',
     '      c.p₁ + c.n ^ 4 == (c.w + c.u) * (c.n + 1) ^ 4 + c.v * (c.n + 2) ^ 4 &&',
     '      c.p₂ + c.n ^ 4 == c.u * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4) ||',
     '    (decide (c.w = 0 ∨ c.y = 0) &&',
     '      c.p₁ + c.n ^ 4 == (c.w + c.u) * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4 && c.p₂ == c.p₁))',
     '',
     'theorem NCert.cert (c : NCert) (h : c.okC = true) :',
     '    Cert (c.n ^ 4) ((c.n + 1) ^ 4) ((c.n + 2) ^ 4) (c.w + c.u + 1) (c.y + c.v + 1) c.w c.y c.q₁ c.q₂ := by',
     '  simp only [NCert.okC, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h',
     '  obtain ⟨⟨⟨⟨⟨⟨ha, hg⟩, hd⟩, h1⟩, h2⟩, hq1⟩, hq2⟩ := h',
     '  exact ⟨ha, hg, by omega, by omega, hd, h1, h2, hq1, hq2⟩', '',
     'theorem NCert.parts (c : NCert) (h : c.ok = true) : c.okC = true ∧',
     '    c.F + c.n ^ 4 = max ((c.w + c.u) * (c.n + 1) ^ 4 + c.v * (c.n + 2) ^ 4)',
     '      (c.u * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4) ∧',
     '    c.g * c.n ^ 4 * 2 + c.n ^ 4 * c.n ^ 4 +',
     '      c.w * c.y * ((c.w + 2 * c.u + 1) * (c.n + 1) ^ 4 + (c.y + 2 * c.v + 1) * (c.n + 2) ^ 4) =',
     '    (c.w + c.u + 1) * (c.y + c.v + 1) * ((c.w + c.u) * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4)',
     '      + c.n ^ 4 ∧',
     '    ((1 ≤ c.w ∧ 1 ≤ c.y) ∧ c.p₁ + c.n ^ 4 = (c.w + c.u) * (c.n + 1) ^ 4 + c.v * (c.n + 2) ^ 4 ∧',
     '        c.p₂ + c.n ^ 4 = c.u * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4 ∨',
     '      (c.w = 0 ∨ c.y = 0) ∧',
     '        c.p₁ + c.n ^ 4 = (c.w + c.u) * (c.n + 1) ^ 4 + (c.y + c.v) * (c.n + 2) ^ 4 ∧ c.p₂ = c.p₁) := by',
     '  simp only [NCert.ok, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h',
     '  obtain ⟨⟨⟨hC, hF⟩, hg⟩, hp⟩ := h',
     '  refine ⟨hC, hF, hg, ?_⟩',
     '  rcases hp with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩',
     '  · exact Or.inl ⟨h1, h2, h3⟩',
     '  · exact Or.inr ⟨h1, h2, h3⟩', '',
     'theorem NCert.sound (c : NCert) (h : c.ok = true) :',
     '    FrobeniusNumber c.F {c.n ^ 4, (c.n + 1) ^ 4, (c.n + 2) ^ 4} := by',
     '  obtain ⟨hC, hF, -, -⟩ := c.parts h',
     '  have C := c.cert hC',
     '  exact frob_uv C.ha C.cop C.det C.rel₁ C.rel₂ C.q₁pos C.q₂pos hF', '',
     'theorem NCert.sound_genus (c : NCert) (h : c.ok = true) :',
     '    genus {c.n ^ 4, (c.n + 1) ^ 4, (c.n + 2) ^ 4} = c.g := by',
     '  obtain ⟨hC, -, hg, -⟩ := c.parts h',
     '  have hG := genus_uv (c.cert hC)',
     '  have ha : 0 < c.n ^ 4 * 2 := by have := (c.cert hC).ha; omega',
     '  apply Nat.eq_of_mul_eq_mul_right ha',
     '  have e1 : genus {c.n ^ 4, (c.n + 1) ^ 4, (c.n + 2) ^ 4} * (c.n ^ 4 * 2)',
     '      = genus {c.n ^ 4, (c.n + 1) ^ 4, (c.n + 2) ^ 4} * c.n ^ 4 * 2 := by ring',
     '  have e2 : c.g * (c.n ^ 4 * 2) = c.g * c.n ^ 4 * 2 := by ring',
     '  rw [e1, e2]; omega', '',
     'theorem NCert.sound_pf (c : NCert) (h : c.ok = true) (x : ℕ) :',
     '    IsPF {c.n ^ 4, (c.n + 1) ^ 4, (c.n + 2) ^ 4} x ↔ x = c.p₁ ∨ x = c.p₂ := by',
     '  obtain ⟨hC, -, -, hp⟩ := c.parts h',
     '  have C := c.cert hC',
     '  have hb : 0 < (c.n + 1) ^ 4 := by positivity',
     '  have hc : 0 < (c.n + 2) ^ 4 := by positivity',
     '  rcases hp with ⟨⟨hw, hy⟩, h1, h2⟩ | ⟨hdeg, h1, h2⟩',
     '  · exact pf_uv C hb hc hw hy h1 h2 x',
     '  · rw [pf_rect_uv C hb hc hdeg h1 x, h2, or_self]', '',
     'theorem NCert.sound_type (c : NCert) (h : c.ok = true) (hne : c.p₁ ≠ c.p₂) :',
     '    Set.ncard {x | IsPF {c.n ^ 4, (c.n + 1) ^ 4, (c.n + 2) ^ 4} x} = 2 := by',
     '  have hset : {x | IsPF {c.n ^ 4, (c.n + 1) ^ 4, (c.n + 2) ^ 4} x} = {c.p₁, c.p₂} := by',
     '    ext x; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]',
     '    exact c.sound_pf h x',
     '  rw [hset, Set.ncard_pair hne]', '',
     '/-- The values `2 ≤ n < 280` of Table A.5 (where `F(S_n^4) ≠ Φ_{n mod 40}(n)`). -/',
     'def exceptions : List ℕ := [' + ', '.join(map(str, FEXC)) + ']', '',
     '/-- The values of `n ≥ 2` where the genus or the pseudo-Frobenius numbers differ from the',
     'closed forms (these are exactly the `n < N_r`). -/',
     'def exceptionsGP : List ℕ := [' + ', '.join(map(str, EXC['excG'])) + ']', '',
     f'/-- Certificates for all `2 ≤ n ≤ {NMAX}`. -/', 'def smallTable : List NCert := [']
L.append(',\n'.join('  ⟨' + ', '.join(map(str, row)) + '⟩' for row in rows))
L += [']', '',
      'theorem smallTable_ok : smallTable.all NCert.ok = true := by decide +kernel', '',
      'theorem smallTable_phi : smallTable.all (fun c => decide (((c.F : ℤ) = Phi c.n) ↔ c.n ∉ exceptions)) = true := by',
      '  decide +kernel', '',
      'theorem smallTable_gam : smallTable.all (fun c => decide (((c.g : ℤ) = Gam c.n) ↔ c.n ∉ exceptionsGP)) = true := by',
      '  decide +kernel', '',
      'theorem smallTable_pf : smallTable.all (fun c => decide (((c.p₁ : ℤ) = PFa c.n ∧ (c.p₂ : ℤ) = PFb c.n) ↔ c.n ∉ exceptionsGP)) = true := by',
      '  decide +kernel', '',
      'theorem smallTable_ne : smallTable.all (fun c => decide (c.n ∉ exceptionsGP → c.p₁ ≠ c.p₂)) = true := by',
      '  decide +kernel', '',
      f'theorem smallTable_covers : ∀ n, 2 ≤ n → n ≤ {NMAX} → ∃ c ∈ smallTable, c.n = n := by',
      '  decide +kernel', '', 'end FrobK4', '']
open(f'{OUT}/K4Small.lean', 'w').write('\n'.join(L))
print('ok', len(rows))
