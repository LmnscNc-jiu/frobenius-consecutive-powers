import Frobenius.K4Classes
import Frobenius.K4ClassesGP
import Frobenius.K4Small

/-!
# Theorem 5.1 (k = 4): Frobenius number, genus and pseudo-Frobenius numbers of
`S_n = ⟨n^4, (n+1)^4, (n+2)^4⟩`

Main results (all `n ≥ 2`):
* `frobenius_k4_iff`: outside the 36 exceptions `F` is the Frobenius number iff `F = Φ(n)`;
* `genus_k4`: outside the 18 values `exceptionsGP`, the genus is `Gam n` (Table A.4);
* `pf_k4`, `type_k4`: outside `exceptionsGP`, the pseudo-Frobenius numbers are exactly
  `PFa n` and `PFb n`, and the type is two;
* `*_ge_280`: the same for every `n ≥ 280` without exceptions;
* `table5`: the rows of Table A.5 of the paper (Frobenius number, genus, pseudo-Frobenius numbers).
-/

namespace FrobK4

open FrobCert

/-- The generators of `S_n = ⟨n^4, (n+1)^4, (n+2)^4⟩`. -/
abbrev gens (n : ℕ) : Set ℕ := {n ^ 4, (n + 1) ^ 4, (n + 2) ^ 4}

theorem frobeniusNumber_unique {F G : ℕ} {s : Set ℕ} (hF : FrobeniusNumber F s)
    (hG : FrobeniusNumber G s) : F = G :=
  IsGreatest.unique hF hG

/-! ### Frobenius number -/

theorem small (n : ℕ) (h2 : 2 ≤ n) (h : n ≤ 318) :
    ∃ F, FrobeniusNumber F (gens n) ∧ (((F : ℤ) = Phi n) ↔ n ∉ exceptions) := by
  obtain ⟨c, hc, rfl⟩ := smallTable_covers n h2 h
  have hok := List.all_eq_true.mp smallTable_ok c hc
  have hphi := List.all_eq_true.mp smallTable_phi c hc
  exact ⟨c.F, c.sound hok, of_decide_eq_true hphi⟩

theorem large (n : ℕ) (hn : 319 ≤ n) : ∃ F, FrobeniusNumber F (gens n) ∧ (F : ℤ) = Phi n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 40 ∧ n = 40 * q + r :=
    ⟨n / 40, n % 40, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 40).symm⟩
  interval_cases r
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_0 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_1 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_2 t
  · exact class_3 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_4 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_5 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 6 := ⟨q - 6, by omega⟩
    exact class_6 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_7 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_8 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_9 t
  · exact class_10 q
  · exact class_11 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_12 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_13 t
  · exact class_14 q
  · exact class_15 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_16 t
  · exact class_17 q
  · exact class_18 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
    exact class_19 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_20 t
  · exact class_21 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_22 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_23 t
  · exact class_24 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_25 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
    exact class_26 t
  · exact class_27 q
  · exact class_28 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_29 t
  · exact class_30 q
  · exact class_31 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_32 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact class_33 t
  · exact class_34 q
  · exact class_35 q
  · exact class_36 q
  · exact class_37 q
  · exact class_38 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 7 := ⟨q - 7, by omega⟩
    exact class_39 t

/-- **Theorem 5.1** (Frobenius number), all `n ≥ 2` outside the exceptions. -/
theorem frobenius_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptions) :
    ∃ F, FrobeniusNumber F (gens n) ∧ (F : ℤ) = Phi n := by
  rcases Nat.lt_or_ge n 319 with h | h
  · obtain ⟨F, hF, hiff⟩ := small n hn (by omega)
    exact ⟨F, hF, hiff.mpr hE⟩
  · exact large n h

theorem frobenius_k4_iff (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptions) (F : ℕ) :
    FrobeniusNumber F (gens n) ↔ (F : ℤ) = Phi n := by
  obtain ⟨G, hG, hGphi⟩ := frobenius_k4 n hn hE
  constructor
  · intro hF; rw [frobeniusNumber_unique hF hG]; exact hGphi
  · intro hF
    have : F = G := by exact_mod_cast hF.trans hGphi.symm
    rw [this]; exact hG

/-- For every `n ≥ 280`, the Frobenius number of `S_n` is `Φ_{n mod 40}(n)`. -/
theorem frobenius_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) (F : ℕ) :
    FrobeniusNumber F (gens n) ↔ (F : ℤ) = Phi n := by
  apply frobenius_k4_iff n (by omega)
  simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-! ### Genus, pseudo-Frobenius numbers and type -/

theorem largeGP (n : ℕ) (hn : 319 ≤ n) :
    (genus (gens n) : ℤ) = Gam n ∧ (∀ x : ℕ, IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n)) ∧
      Set.ncard {x | IsPF (gens n) x} = 2 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 40 ∧ n = 40 * q + r :=
    ⟨n / 40, n % 40, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 40).symm⟩
  interval_cases r
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_0 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_1 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_2 t
  · exact classGP_3 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_4 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_5 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 6 := ⟨q - 6, by omega⟩
    exact classGP_6 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_7 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_8 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_9 t
  · exact classGP_10 q
  · exact classGP_11 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_12 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_13 t
  · exact classGP_14 q
  · exact classGP_15 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_16 t
  · exact classGP_17 q
  · exact classGP_18 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
    exact classGP_19 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_20 t
  · exact classGP_21 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_22 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_23 t
  · exact classGP_24 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_25 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
    exact classGP_26 t
  · exact classGP_27 q
  · exact classGP_28 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_29 t
  · exact classGP_30 q
  · exact classGP_31 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_32 t
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    exact classGP_33 t
  · exact classGP_34 q
  · exact classGP_35 q
  · exact classGP_36 q
  · exact classGP_37 q
  · exact classGP_38 q
  · obtain ⟨t, rfl⟩ : ∃ t, q = t + 7 := ⟨q - 7, by omega⟩
    exact classGP_39 t

theorem smallGP (n : ℕ) (h2 : 2 ≤ n) (h : n ≤ 318) (hE : n ∉ exceptionsGP) :
    (genus (gens n) : ℤ) = Gam n ∧ (∀ x : ℕ, IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n)) ∧
      Set.ncard {x | IsPF (gens n) x} = 2 := by
  obtain ⟨c, hc, rfl⟩ := smallTable_covers n h2 h
  have hok := List.all_eq_true.mp smallTable_ok c hc
  have hg := (of_decide_eq_true (List.all_eq_true.mp smallTable_gam c hc)).mpr hE
  have hp := (of_decide_eq_true (List.all_eq_true.mp smallTable_pf c hc)).mpr hE
  have hne := of_decide_eq_true (List.all_eq_true.mp smallTable_ne c hc) hE
  refine ⟨?_, ?_, c.sound_type hok hne⟩
  · rw [c.sound_genus hok]; exact hg
  · intro x
    rw [c.sound_pf hok x, ← hp.1, ← hp.2]
    constructor
    · rintro (h | h) <;> [left; right] <;> exact_mod_cast h
    · rintro (h | h) <;> [left; right] <;> exact_mod_cast h

theorem gp_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) :
    (genus (gens n) : ℤ) = Gam n ∧ (∀ x : ℕ, IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n)) ∧
      Set.ncard {x | IsPF (gens n) x} = 2 := by
  rcases Nat.lt_or_ge n 319 with h | h
  · exact smallGP n hn (by omega) hE
  · exact largeGP n h

/-- **Theorem 5.1** (genus, Table A.4). -/
theorem genus_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) : (genus (gens n) : ℤ) = Gam n :=
  (gp_k4 n hn hE).1

/-- **Theorem 5.1** (pseudo-Frobenius numbers). -/
theorem pf_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) (x : ℕ) :
    IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n) :=
  (gp_k4 n hn hE).2.1 x

/-- **Theorem 5.1** (type two). -/
theorem type_k4 (n : ℕ) (hn : 2 ≤ n) (hE : n ∉ exceptionsGP) :
    Set.ncard {x | IsPF (gens n) x} = 2 :=
  (gp_k4 n hn hE).2.2

theorem notMem_exceptionsGP_of_ge (n : ℕ) (hn : 120 ≤ n) : n ∉ exceptionsGP := by
  simp only [exceptionsGP, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem genus_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) : (genus (gens n) : ℤ) = Gam n :=
  genus_k4 n (by omega) (notMem_exceptionsGP_of_ge n (by omega))

theorem pf_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) (x : ℕ) :
    IsPF (gens n) x ↔ ((x : ℤ) = PFa n ∨ (x : ℤ) = PFb n) :=
  pf_k4 n (by omega) (notMem_exceptionsGP_of_ge n (by omega)) x

theorem type_k4_ge_280 (n : ℕ) (hn : 280 ≤ n) : Set.ncard {x | IsPF (gens n) x} = 2 :=
  type_k4 n (by omega) (notMem_exceptionsGP_of_ge n (by omega))

/-! ### Table A.5 -/

/-- Table A.5 of the paper: `(n, F(S_n), g(S_n), PF(S_n))` at the 36 exceptional `n`. -/
def table5 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (2, 1199, 600, [1199]),
  (4, 28559, 14280, [28559]),
  (5, 78308, 41713, [75375, 78308]),
  (6, 362399, 181200, [362399]),
  (7, 486079, 247008, [423230, 486079]),
  (8, 994223, 502480, [719199, 994223]),
  (9, 1897924, 965342, [1496925, 1897924]),
  (12, 12005295, 6071192, [11340175, 12005295]),
  (13, 15400797, 7729559, [12210261, 15400797]),
  (16, 48247935, 24979344, [46196687, 48247935]),
  (19, 176868200, 90813516, [173824201, 176868200]),
  (20, 206091151, 107576840, [205384719, 206091151]),
  (22, 284935071, 147692384, [280329727, 284935071]),
  (23, 342540864, 184580645, [325803453, 342540864]),
  (25, 720624113, 365363593, [669456150, 720624113]),
  (26, 1161433871, 587358984, [1110824047, 1161433871]),
  (29, 1465271324, 739585479, [1183364327, 1465271324]),
  (32, 3555061055, 1782545568, [3164578735, 3555061055]),
  (33, 3101611290, 1589581610, [3066924927, 3101611290]),
  (39, 21173668803, 10589583194, [20811444802, 21173668803]),
  (46, 32050880511, 16070735744, [29273174287, 32050880511]),
  (59, 133546213800, 67447447193, [126716185803, 133546213800]),
  (66, 264911458415, 133753152888, [250579124543, 264911458415]),
  (79, 1361182355203, 680612207996, [1336258323201, 1361182355203]),
  (86, 1259471988319, 638300005616, [1214027215599, 1259471988319]),
  (106, 4336407350223, 2202885588968, [4229545319455, 4336407350223]),
  (119, 15421051483202, 7758023870871, [15311876011205, 15421051483202]),
  (126, 12081180904127, 6147168377184, [11878984508111, 12081180904127]),
  (146, 28978028490031, 14762080143704, [28660855053567, 28978028490031]),
  (159, 87210392140803, 43605360473600, [85572320844799, 87210392140803]),
  (166, 62174118427935, 31701431081168, [61768694427823, 62174118427935]),
  (186, 122373887517839, 62440330921416, [122003067302879, 122373887517839]),
  (199, 331419997320004, 166352159756000, [327700799319999, 331419997320004]),
  (206, 224863553039743, 114800426055488, [224817197550735, 224863553039743]),
  (239, 987108245164805, 496747302583680, [981038406700799, 987108245164805]),
  (279, 2484608575579206, 1252652331872480, [2478372895947199, 2484608575579206])
]

theorem table5_spec : ∀ row ∈ table5, ∃ c ∈ smallTable, c.n = row.1 ∧ c.F = row.2.1 ∧
    c.g = row.2.2.1 ∧ c.p₁ ∈ row.2.2.2 ∧ c.p₂ ∈ row.2.2.2 ∧ ∀ z ∈ row.2.2.2, z = c.p₁ ∨ z = c.p₂ := by
  decide +kernel

theorem table5_n : table5.map (·.1) = exceptions := by decide +kernel

/-- **Table A.5**: Frobenius number, genus and pseudo-Frobenius numbers at the exceptions. -/
theorem table5_correct : ∀ row ∈ table5,
    FrobeniusNumber row.2.1 (gens row.1) ∧ genus (gens row.1) = row.2.2.1 ∧
      ∀ x : ℕ, IsPF (gens row.1) x ↔ x ∈ row.2.2.2 := by
  intro row hrow
  obtain ⟨c, hc, h1, h2, h3, h4, h5, h6⟩ := table5_spec row hrow
  have hok := List.all_eq_true.mp smallTable_ok c hc
  rw [← h1, ← h2, ← h3]
  refine ⟨c.sound hok, c.sound_genus hok, fun x => ?_⟩
  rw [c.sound_pf hok x]
  constructor
  · rintro (rfl | rfl)
    · exact h4
    · exact h5
  · intro hx; exact h6 x hx

/-- At the exceptions the Frobenius number differs from `Φ`. -/
theorem frobenius_k4_exceptions : ∀ n ∈ exceptions, ∀ F, FrobeniusNumber F (gens n) → (F : ℤ) ≠ Phi n := by
  intro n hn F hF
  have h2 : 2 ≤ n ∧ n ≤ 318 := by
    simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false] at hn; omega
  obtain ⟨G, hG, hiff⟩ := small n h2.1 h2.2
  rw [frobeniusNumber_unique hF hG]
  intro hc; exact (hiff.mp hc) hn

end FrobK4
