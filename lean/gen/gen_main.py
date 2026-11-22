"""Generate Frobenius/K4.lean (final theorems).  Table A.5 is read from the paper's LaTeX table.
Usage: python3 gen_main.py STARTS_JSON TAB_EXC_TEX OUT_LEAN"""
import json, re, sys
starts = json.load(open(sys.argv[1]))
rows = []
for line in open(sys.argv[2]):
    parts = [p.strip() for p in line.replace('\\\\', '').split('&')]
    if len(parts) == 4:
        nn, F, g, pf = int(parts[0]), int(parts[1]), int(parts[2]), [int(x) for x in parts[3].split(',')]
        rows.append((nn, F, g, pf))
assert len(rows) == 36

def cases(mk):
    out = []
    for r in range(40):
        m0 = (starts[str(r)] - r) // 40
        if m0 == 0:
            out.append(f'  · exact {mk(r, "q")}')
        else:
            out.append(f'  · obtain ⟨t, rfl⟩ : ∃ t, q = t + {m0} := ⟨q - {m0}, by omega⟩')
            out.append(f'    exact {mk(r, "t")}')
    return out

L = ['import Frobenius.K4Classes', 'import Frobenius.K4ClassesGP', 'import Frobenius.K4Small', '',
'/-!', '# Theorem 5.1 (k = 4): Frobenius number, genus and pseudo-Frobenius numbers of',
'`S_n = ⟨n^4, (n+1)^4, (n+2)^4⟩`', '',
'Main results (all `n ≥ 2`):',
'* `frobenius_k4_iff`: outside the 36 exceptions `F` is the Frobenius number iff `F = Φ(n)`;',
'* `genus_k4`: outside the 18 values `exceptionsGP`, the genus is `Gam n` (Table A.4);',
'* `pf_k4`, `type_k4`: outside `exceptionsGP`, the pseudo-Frobenius numbers are exactly',
'  `PFa n` and `PFb n`, and the type is two;',
'* `*_ge_280`: the same for every `n ≥ 280` without exceptions;',
'* `table5`: the rows of Table A.5 of the paper (Frobenius number, genus, pseudo-Frobenius numbers).',
'-/', '', 'namespace FrobK4', '', 'open FrobCert', '',
'/-- The generators of `S_n = ⟨n^4, (n+1)^4, (n+2)^4⟩`. -/',
'abbrev gens (n : ℕ) : Set ℕ := {n ^ 4, (n + 1) ^ 4, (n + 2) ^ 4}', '',
'theorem frobeniusNumber_unique {F G : ℕ} {s : Set ℕ} (hF : FrobeniusNumber F s)',
'    (hG : FrobeniusNumber G s) : F = G :=', '  IsGreatest.unique hF hG', '',
'/-! ### Frobenius number -/', '',
'theorem small (n : ℕ) (h2 : 2 ≤ n) (h : n ≤ 318) :',
'    ∃ F, FrobeniusNumber F (gens n) ∧ (((F : ℤ) = Phi n) ↔ n ∉ exceptions) := by',
'  obtain ⟨c, hc, rfl⟩ := smallTable_covers n h2 h',
'  have hok := List.all_eq_true.mp smallTable_ok c hc',
'  have hphi := List.all_eq_true.mp smallTable_phi c hc',
'  exact ⟨c.F, c.sound hok, of_decide_eq_true hphi⟩', '',
'theorem large (n : ℕ) (hn : 319 ≤ n) : ∃ F, FrobeniusNumber F (gens n) ∧ (F : ℤ) = Phi n := by',
'  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 40 ∧ n = 40 * q + r :=',
'    ⟨n / 40, n % 40, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 40).symm⟩',
'  interval_cases r']
L += cases(lambda r, v: f'class_{r} {v}')
L += ['',
'/-- **Theorem 5.1** (Frobenius number), all `n ≥ 2` outside the exceptions. -/',
'theorem frobenius_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptions) :',
'    ∃ F, FrobeniusNumber F (gens n) ∧ (F : ℤ) = Phi n := by',
'  rcases Nat.lt_or_ge n 319 with h | h',
'  · obtain ⟨F, hF, hiff⟩ := small n hn (by omega)',
'    exact ⟨F, hF, hiff.mpr hE⟩',
'  · exact large n h', '',
'theorem frobenius_k4_iff (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptions) (F : ℕ) :',
'    FrobeniusNumber F (gens n) ↔ (F : ℤ) = Phi n := by',
'  obtain ⟨G, hG, hGphi⟩ := frobenius_k4 n hn hE',
'  constructor',
'  · intro hF; rw [frobeniusNumber_unique hF hG]; exact hGphi',
'  · intro hF',
'    have : F = G := by exact_mod_cast hF.trans hGphi.symm',
'    rw [this]; exact hG', '',
'/-- For every `n ≥ 280`, the Frobenius number of `S_n` is `Φ_{n mod 40}(n)`. -/',
'theorem frobenius_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) (F : ℕ) :',
'    FrobeniusNumber F (gens n) ↔ (F : ℤ) = Phi n := by',
'  apply frobenius_k4_iff n (by omega)',
'  simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false]',
'  omega', '',
'/-! ### Genus, pseudo-Frobenius numbers and type -/', '',
'theorem largeGP (n : ℕ) (hn : 319 ≤ n) :',
'    (genus (gens n) : ℤ) = Gam n ∧ (∀ x : ℕ, IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n)) ∧',
'      Set.ncard {x | IsPF (gens n) x} = 2 := by',
'  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 40 ∧ n = 40 * q + r :=',
'    ⟨n / 40, n % 40, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 40).symm⟩',
'  interval_cases r']
L += cases(lambda r, v: f'classGP_{r} {v}')
L += ['',
'theorem smallGP (n : ℕ) (h2 : 2 ≤ n) (h : n ≤ 318) (hE : n ∉ exceptionsGP) :',
'    (genus (gens n) : ℤ) = Gam n ∧ (∀ x : ℕ, IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n)) ∧',
'      Set.ncard {x | IsPF (gens n) x} = 2 := by',
'  obtain ⟨c, hc, rfl⟩ := smallTable_covers n h2 h',
'  have hok := List.all_eq_true.mp smallTable_ok c hc',
'  have hg := (of_decide_eq_true (List.all_eq_true.mp smallTable_gam c hc)).mpr hE',
'  have hp := (of_decide_eq_true (List.all_eq_true.mp smallTable_pf c hc)).mpr hE',
'  have hne := of_decide_eq_true (List.all_eq_true.mp smallTable_ne c hc) hE',
'  refine ⟨?_, ?_, c.sound_type hok hne⟩',
'  · rw [c.sound_genus hok]; exact hg',
'  · intro x',
'    rw [c.sound_pf hok x, ← hp.1, ← hp.2]',
'    constructor',
'    · rintro (h | h) <;> [left; right] <;> exact_mod_cast h',
'    · rintro (h | h) <;> [left; right] <;> exact_mod_cast h', '',
'theorem gp_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) :',
'    (genus (gens n) : ℤ) = Gam n ∧ (∀ x : ℕ, IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n)) ∧',
'      Set.ncard {x | IsPF (gens n) x} = 2 := by',
'  rcases Nat.lt_or_ge n 319 with h | h',
'  · exact smallGP n hn (by omega) hE',
'  · exact largeGP n h', '',
'/-- **Theorem 5.1** (genus, Table A.4). -/',
'theorem genus_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) : (genus (gens n) : ℤ) = Gam n :=',
'  (gp_k4 n hn hE).1', '',
'/-- **Theorem 5.1** (pseudo-Frobenius numbers). -/',
'theorem pf_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) (x : ℕ) :',
'    IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n) :=',
'  (gp_k4 n hn hE).2.1 x', '',
'/-- **Theorem 5.1** (type two). -/',
'theorem type_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) :',
'    Set.ncard {x | IsPF (gens n) x} = 2 :=',
'  (gp_k4 n hn hE).2.2', '',
'theorem notMem_exceptionsGP_of_ge (n : ℕ) (hn : 120 ≤ n) : n ∉ exceptionsGP := by',
'  simp only [exceptionsGP, List.mem_cons, List.not_mem_nil, or_false]', '  omega', '',
'theorem genus_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) : (genus (gens n) : ℤ) = Gam n :=',
'  genus_k4 n (by omega) (notMem_exceptionsGP_of_ge n (by omega))', '',
'theorem pf_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) (x : ℕ) :',
'    IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n) :=',
'  pf_k4 n (by omega) (notMem_exceptionsGP_of_ge n (by omega)) x', '',
'theorem type_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) : Set.ncard {x | IsPF (gens n) x} = 2 :=',
'  type_k4 n (by omega) (notMem_exceptionsGP_of_ge n (by omega))', '',
'/-! ### Table A.5 -/', '',
'/-- Table A.5 of the paper: `(n, F(S_n), g(S_n), PF(S_n))` at the 36 exceptional `n`. -/',
'def table5 : List (ℕ × ℕ × ℕ × List ℕ) := [']
L.append(',\n'.join(f'  ({n_}, {F}, {g}, [{", ".join(map(str, pf))}])' for n_, F, g, pf in rows))
L += [']', '',
'theorem table5_spec : ∀ row ∈ table5, ∃ c ∈ smallTable, c.n = row.1 ∧ c.F = row.2.1 ∧',
'    c.g = row.2.2.1 ∧ c.p₁ ∈ row.2.2.2 ∧ c.p₂ ∈ row.2.2.2 ∧ ∀ z ∈ row.2.2.2, z = c.p₁ ∨ z = c.p₂ := by',
'  decide +kernel', '',
'theorem table5_n : table5.map (·.1) = exceptions := by decide +kernel', '',
'/-- **Table A.5**: Frobenius number, genus and pseudo-Frobenius numbers at the exceptions. -/',
'theorem table5_correct : ∀ row ∈ table5,',
'    FrobeniusNumber row.2.1 (gens row.1) ∧ genus (gens row.1) = row.2.2.1 ∧',
'      ∀ x : ℕ, IsPF (gens row.1) x ↔ x ∈ row.2.2.2 := by',
'  intro row hrow',
'  obtain ⟨c, hc, h1, h2, h3, h4, h5, h6⟩ := table5_spec row hrow',
'  have hok := List.all_eq_true.mp smallTable_ok c hc',
'  rw [← h1, ← h2, ← h3]',
'  refine ⟨c.sound hok, c.sound_genus hok, fun x => ?_⟩',
'  rw [c.sound_pf hok x]',
'  constructor',
'  · rintro (rfl | rfl)',
'    · exact h4',
'    · exact h5',
'  · intro hx; exact h6 x hx', '',
'/-- At the exceptions the Frobenius number differs from `Φ`. -/',
'theorem frobenius_k4_exceptions : ∀ n ∈ exceptions, ∀ F, FrobeniusNumber F (gens n) → (F : ℤ) ≠ Phi n := by',
'  intro n hn F hF',
'  have h2 : 2 ≤ n ∧ n ≤ 318 := by',
'    simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false] at hn; omega',
'  obtain ⟨G, hG, hiff⟩ := small n h2.1 h2.2',
'  rw [frobeniusNumber_unique hF hG]',
'  intro hc; exact (hiff.mp hc) hn', '',
'end FrobK4', '']
open(sys.argv[3], 'w').write('\n'.join(L))
print('ok')
