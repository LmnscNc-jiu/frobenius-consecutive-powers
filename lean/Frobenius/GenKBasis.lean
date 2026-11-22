import Frobenius.GenKRelations

/-!
# Proposition 3.1(c): two independent relations

For every shift `c ∉ {0, 1}` there are relations `V₁` of degree `≤ ⌊k/2⌋` and `V₂` of degree
`≤ ⌈k/2⌉` with `det(V₁, V₂) = κ X^k`, `κ ≠ 0`.

Proof (as in the paper, but without primitive parts): if every relation of degree `≤ ⌈k/2⌉` were
parallel to `V₁`, all of them would be pairwise parallel; then the leading-coefficient map in each
degree `e` has rank `≤ 1`, so the spaces `Σ_e` of relations of degree `≤ e` grow by at most one
dimension per degree. Since `Σ_{⌊k/2⌋-1} = 0` (normality) this gives
`dim Σ_{⌈k/2⌉} ≤ ⌈k/2⌉ - ⌊k/2⌋ + 1`, contradicting the count `dim Σ_{⌈k/2⌉} ≥ 2⌈k/2⌉ + 2 - k`.
-/

open Polynomial Module

namespace GenK

noncomputable section

variable {c : ℚ}

/-- the determinant of two polynomial vectors -/
def det2 (v w : ℚ[X] × ℚ[X]) : ℚ[X] := v.1 * w.2 - w.1 * v.2

/-- relations of degree `≤ e` -/
def RelSub (c : ℚ) (k e : ℕ) : Submodule ℚ (ℚ[X] × ℚ[X]) where
  carrier := {v | IsRel c k v.1 v.2 ∧ v.1.natDegree ≤ e ∧ v.2.natDegree ≤ e}
  add_mem' := by
    rintro ⟨p, z⟩ ⟨p', z'⟩ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, (natDegree_add_le _ _).trans (max_le h2 h2'),
      (natDegree_add_le _ _).trans (max_le h3 h3')⟩
    show X ^ k ∣ (p + p') * (X + 1) ^ k + (z + z') * (X + C c) ^ k
    have := dvd_add h1 h1'
    convert this using 1; ring
  zero_mem' := ⟨by simp [IsRel], by simp, by simp⟩
  smul_mem' := by
    rintro a ⟨p, z⟩ ⟨h1, h2, h3⟩
    refine ⟨?_, (natDegree_smul_le _ _).trans h2, (natDegree_smul_le _ _).trans h3⟩
    show X ^ k ∣ (a • p) * (X + 1) ^ k + (a • z) * (X + C c) ^ k
    have := dvd_mul_of_dvd_right h1 (C a)
    rw [smul_eq_C_mul, smul_eq_C_mul]
    convert this using 1; ring

theorem mem_RelSub {k e : ℕ} {v : ℚ[X] × ℚ[X]} :
    v ∈ RelSub c k e ↔ IsRel c k v.1 v.2 ∧ v.1.natDegree ≤ e ∧ v.2.natDegree ≤ e := Iff.rfl

theorem RelSub_mono {k e e' : ℕ} (h : e ≤ e') : RelSub c k e ≤ RelSub c k e' :=
  fun _ hv => ⟨hv.1, hv.2.1.trans h, hv.2.2.trans h⟩

/-- coefficients `0..e` of both entries -/
def coefMap (e : ℕ) : (ℚ[X] × ℚ[X]) →ₗ[ℚ] (Fin (e + 1) → ℚ) × (Fin (e + 1) → ℚ) where
  toFun v := (fun i => v.1.coeff i, fun i => v.2.coeff i)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

theorem coefMap_injOn {k e : ℕ} : Function.Injective ((coefMap e).domRestrict (RelSub c k e)) := by
  intro v w hvw
  simp only [LinearMap.domRestrict_apply, coefMap, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
    at hvw
  apply Subtype.ext
  apply Prod.ext
  · ext i
    by_cases hi : i ≤ e
    · exact congrFun hvw.1 ⟨i, by omega⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by have := v.2.2.1; omega),
        coeff_eq_zero_of_natDegree_lt (by have := w.2.2.1; omega)]
  · ext i
    by_cases hi : i ≤ e
    · exact congrFun hvw.2 ⟨i, by omega⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by have := v.2.2.2; omega),
        coeff_eq_zero_of_natDegree_lt (by have := w.2.2.2; omega)]

instance (k e : ℕ) : FiniteDimensional ℚ (RelSub c k e) :=
  Module.Finite.of_injective _ (coefMap_injOn (k := k) (e := e))

/-- Lower bound on the dimension of the space of relations of degree `≤ d`. -/
theorem finrank_RelSub_ge (k d : ℕ) : 2 * (d + 1) - k ≤ finrank ℚ (RelSub c k d) := by
  set f := relMap c k d
  have hrn := f.finrank_range_add_finrank_ker
  have hrange : finrank ℚ (LinearMap.range f) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range f); simpa using this
  have hdom : finrank ℚ (degreeLT ℚ (d + 1) × degreeLT ℚ (d + 1)) = 2 * (d + 1) := by
    rw [Module.finrank_prod, (degreeLTEquiv ℚ (d + 1)).finrank_eq, Module.finrank_fin_fun]; ring
  -- injection ker f → RelSub c k d
  let g : LinearMap.ker f →ₗ[ℚ] RelSub c k d :=
    { toFun := fun v => ⟨((v.1.1 : ℚ[X]), (v.1.2 : ℚ[X])), by
        refine ⟨?_, ?_, ?_⟩
        · rw [IsRel, X_pow_dvd_iff]
          intro i hi
          have h0 : f v.1 = 0 := LinearMap.mem_ker.mp v.2
          have := congrFun h0 ⟨i, hi⟩
          simp only [f, relMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
          simpa using this
        · have := v.1.1.2; rw [mem_degreeLT] at this
          exact natDegree_le_of_degree_le (Order.lt_succ_iff.mp (by exact_mod_cast this))
        · have := v.1.2.2; rw [mem_degreeLT] at this
          exact natDegree_le_of_degree_le (Order.lt_succ_iff.mp (by exact_mod_cast this))⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hg : Function.Injective g := by
    intro x y hxy
    have h' := congrArg Subtype.val hxy
    exact Subtype.ext (Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h')))
  have := LinearMap.finrank_le_finrank_of_injective hg
  omega

/-- top coefficient of a determinant -/
theorem coeff_det2 {e : ℕ} {v w : ℚ[X] × ℚ[X]} (hv1 : v.1.natDegree ≤ e) (hv2 : v.2.natDegree ≤ e)
    (hw1 : w.1.natDegree ≤ e) (hw2 : w.2.natDegree ≤ e) :
    (det2 v w).coeff (e + e) = v.1.coeff e * w.2.coeff e - w.1.coeff e * v.2.coeff e := by
  simp only [det2, coeff_sub, coeff_mul_add_eq_of_natDegree_le hv1 hw2,
    coeff_mul_add_eq_of_natDegree_le hw1 hv2]

/-- leading-coefficient map in degree `e` -/
def lcMap (k e : ℕ) : RelSub c k e →ₗ[ℚ] ℚ × ℚ where
  toFun v := (v.1.1.coeff e, v.1.2.coeff e)
  map_add' x y := by simp
  map_smul' c x := by simp

theorem lcMap_apply {k e : ℕ} (v : RelSub c k e) : lcMap k e v = (v.1.1.coeff e, v.1.2.coeff e) := rfl

/-- One step of the filtration. -/
theorem finrank_step {k e : ℕ} (_he : 1 ≤ e)
    (hpair : ∀ v ∈ RelSub c k e, ∀ w ∈ RelSub c k e, det2 v w = 0) :
    finrank ℚ (RelSub c k e) ≤ finrank ℚ (RelSub c k (e - 1)) + 1 := by
  set f := lcMap k e
  have hrn := f.finrank_range_add_finrank_ker
  -- kernel injects into RelSub c k (e - 1)
  let g : LinearMap.ker f →ₗ[ℚ] RelSub c k (e - 1) :=
    { toFun := fun v => ⟨v.1.1, by
        have hv := v.1.2
        have h0 : lcMap k e v.1 = 0 := LinearMap.mem_ker.mp v.2
        rw [lcMap_apply, Prod.mk_eq_zero] at h0
        exact ⟨hv.1, natDegree_le_pred hv.2.1 h0.1, natDegree_le_pred hv.2.2 h0.2⟩⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hg : Function.Injective g := by
    intro x y hxy
    have h' := congrArg (fun z : RelSub c k (e - 1) => (z : ℚ[X] × ℚ[X])) hxy
    exact Subtype.ext (Subtype.ext h')
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hrange : finrank ℚ (LinearMap.range f) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h2 : finrank ℚ (LinearMap.range f) = finrank ℚ (ℚ × ℚ) := by
      have := Submodule.finrank_le (LinearMap.range f)
      rw [Module.finrank_prod, Module.finrank_self] at this ⊢
      omega
    have htop := Submodule.eq_top_of_finrank_eq h2
    obtain ⟨v, hv⟩ : (1, 0) ∈ LinearMap.range f := by rw [htop]; trivial
    obtain ⟨w, hw⟩ : (0, 1) ∈ LinearMap.range f := by rw [htop]; trivial
    rw [lcMap_apply, Prod.mk.injEq] at hv hw
    have hc := coeff_det2 v.2.2.1 v.2.2.2 w.2.2.1 w.2.2.2
    rw [hpair v.1 v.2 w.1 w.2, hv.1, hv.2, hw.1, hw.2] at hc
    simp at hc
  omega

theorem plucker (V1 v w : ℚ[X] × ℚ[X]) (hV1 : V1 ≠ 0) (h1 : det2 V1 v = 0) (h2 : det2 V1 w = 0) :
    det2 v w = 0 := by
  have e1 : V1.1 * det2 v w = v.1 * det2 V1 w - w.1 * det2 V1 v := by simp only [det2]; ring
  have e2 : V1.2 * det2 v w = v.2 * det2 V1 w - w.2 * det2 V1 v := by simp only [det2]; ring
  rw [h1, h2] at e1 e2
  simp only [mul_zero, sub_zero] at e1 e2
  by_contra hne
  apply hV1
  exact Prod.ext ((mul_eq_zero.mp e1).resolve_right hne) ((mul_eq_zero.mp e2).resolve_right hne)

theorem X_pow_dvd_det2 {k : ℕ} {v w : ℚ[X] × ℚ[X]} (hv : IsRel c k v.1 v.2) (hw : IsRel c k w.1 w.2) :
    X ^ k ∣ det2 v w := by
  have hU : IsCoprime (X ^ k : ℚ[X]) ((X + 1) ^ k) := by
    apply IsCoprime.pow
    have := isCoprime_X_sub_C_of_isUnit_sub (R := ℚ) (a := 0) (b := -1) (by norm_num)
    simpa using this
  apply hU.dvd_of_dvd_mul_right
  have e : det2 v w * (X + 1) ^ k =
      w.2 * (v.1 * (X + 1) ^ k + v.2 * (X + C c) ^ k) - v.2 * (w.1 * (X + 1) ^ k + w.2 * (X + C c) ^ k) := by
    simp only [det2]; ring
  rw [e]
  exact dvd_sub (dvd_mul_of_dvd_right hv _) (dvd_mul_of_dvd_right hw _)

/-- **Proposition 3.1(c).** -/
theorem exists_basis (c : ℚ) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (k : ℕ) (hk : 2 ≤ k) :
    ∃ V1 V2 : ℚ[X] × ℚ[X], V1 ∈ RelSub c k (k / 2) ∧ V2 ∈ RelSub c k ((k + 1) / 2) ∧
      ∃ κ : ℚ, κ ≠ 0 ∧ det2 V1 V2 = C κ * X ^ k := by
  set d1 := k / 2
  set d2 := (k + 1) / 2
  have hsum : d1 + d2 = k := by omega
  have hd1 : 1 ≤ d1 := by omega
  obtain ⟨P, Z, hne, hP, hZ, hrel⟩ := exists_rel c k d1 (by omega)
  set V1 : ℚ[X] × ℚ[X] := (P, Z)
  have hV1 : V1 ∈ RelSub c k d1 := ⟨hrel, hP, hZ⟩
  have hV1ne : V1 ≠ 0 := by
    intro h; rcases hne with h' | h'
    · exact h' (congrArg Prod.fst h)
    · exact h' (congrArg Prod.snd h)
  have hV1' : V1 ∈ RelSub c k d2 := RelSub_mono (by omega) hV1
  have hex : ∃ V2 ∈ RelSub c k d2, det2 V1 V2 ≠ 0 := by
    by_contra hall
    push Not at hall
    have hpair : ∀ e ≤ d2, ∀ v ∈ RelSub c k e, ∀ w ∈ RelSub c k e, det2 v w = 0 := by
      intro e he v hv w hw
      exact plucker V1 v w hV1ne (hall v (RelSub_mono he hv)) (hall w (RelSub_mono he hw))
    have hbase : finrank ℚ (RelSub c k (d1 - 1)) = 0 := by
      rw [Submodule.finrank_eq_zero]
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨h1, h2⟩ := normality hc0 hc1 (by omega) hv.2.1 hv.2.2 hv.1
      simp [Prod.ext_iff, h1, h2]
    have hind : ∀ j, d1 - 1 + j ≤ d2 → finrank ℚ (RelSub c k (d1 - 1 + j)) ≤ j := by
      intro j
      induction j with
      | zero => intro _; simp [hbase]
      | succ j ih =>
        intro hj
        have hstep := finrank_step (k := k) (e := d1 - 1 + (j + 1)) (by omega)
          (hpair _ hj)
        have : d1 - 1 + (j + 1) - 1 = d1 - 1 + j := by omega
        rw [this] at hstep
        have := ih (by omega)
        omega
    have hup := hind (d2 - d1 + 1) (by omega)
    have : d1 - 1 + (d2 - d1 + 1) = d2 := by omega
    rw [this] at hup
    have hlow := finrank_RelSub_ge (c := c) k d2
    omega
  obtain ⟨V2, hV2, hdet⟩ := hex
  refine ⟨V1, V2, hV1, hV2, ?_⟩
  obtain ⟨q, hq⟩ := X_pow_dvd_det2 hV1.1 hV2.1
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact hdet hq
  have hdeg : (det2 V1 V2).natDegree ≤ k := by
    simp only [det2]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_mul_le.trans (by have := hV1.2.1; have := hV2.2.2; omega)
    · exact natDegree_mul_le.trans (by have := hV2.2.1; have := hV1.2.2; omega)
  have hqdeg : q.natDegree = 0 := by
    rw [hq, natDegree_mul (pow_ne_zero _ X_ne_zero) hq0, natDegree_X_pow] at hdeg
    omega
  refine ⟨q.coeff 0, ?_, ?_⟩
  · intro h0
    apply hq0
    rw [eq_C_of_natDegree_eq_zero hqdeg, h0, C_0]
  · rw [hq]
    conv_lhs => rw [eq_C_of_natDegree_eq_zero hqdeg]
    ring


/-- **Proposition 3.1(c)** with the exact degrees: `deg V₁ = ⌊k/2⌋`, `deg V₂ = ⌈k/2⌉`
(where `deg (P, Z) = max (deg P) (deg Z)`). -/
theorem exists_basis_exact (c : ℚ) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (k : ℕ) (hk : 2 ≤ k) :
    ∃ V1 V2 : ℚ[X] × ℚ[X], IsRel c k V1.1 V1.2 ∧ IsRel c k V2.1 V2.2 ∧
      max V1.1.natDegree V1.2.natDegree = k / 2 ∧
      max V2.1.natDegree V2.2.natDegree = (k + 1) / 2 ∧
      ∃ κ : ℚ, κ ≠ 0 ∧ det2 V1 V2 = C κ * X ^ k := by
  obtain ⟨V1, V2, hV1, hV2, κ, hκ, hdet⟩ := exists_basis c hc0 hc1 k hk
  refine ⟨V1, V2, hV1.1, hV2.1, ?_, ?_, κ, hκ, hdet⟩
  · apply le_antisymm (max_le hV1.2.1 hV1.2.2)
    by_contra hlt
    push Not at hlt
    obtain ⟨h1, h2⟩ := normality hc0 hc1 (k := k) (d := k / 2 - 1) (by omega)
      (by have := le_max_left V1.1.natDegree V1.2.natDegree; omega)
      (by have := le_max_right V1.1.natDegree V1.2.natDegree; omega) hV1.1
    have : det2 V1 V2 = 0 := by simp [det2, h1, h2]
    rw [hdet] at this
    exact hκ (by simpa using this)
  · apply le_antisymm (max_le hV2.2.1 hV2.2.2)
    have hk' : (det2 V1 V2).natDegree = k := by rw [hdet]; exact natDegree_C_mul_X_pow k κ hκ
    have hle : (det2 V1 V2).natDegree ≤ k / 2 + max V2.1.natDegree V2.2.natDegree := by
      simp only [det2]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_mul_le.trans (add_le_add hV1.2.1 (le_max_right _ _))
      · refine natDegree_mul_le.trans ?_
        rw [add_comm]
        exact add_le_add hV1.2.2 (le_max_left _ _)
    omega

end

end GenK
