import Mathlib

/-!
# Polynomial relations (Proposition 3.1)

Fix a rational number `c ∉ {0, 1}`. A *relation* of degree `≤ d` is a pair `(P, Z)` of rational
polynomials of degree `≤ d` with `X^k ∣ P (X+1)^k + Z (X+c)^k`. The case of three consecutive
`k`-th powers is `c = 2`; the case `⟨n^k, (n+p)^k, (n+q)^k⟩` reduces to `c = q/p` by the
substitution `x = p y` (see `GenKLattice`).

* `exists_rel`   : (Prop. 3.1(a)) if `k < 2d + 2` there is a nonzero relation of degree `≤ d`;
* `normality`    : (Prop. 3.1(b)) if `2d + 2 ≤ k` every relation of degree `≤ d` is zero.

The proof of `normality` follows the paper: the substitution `x = s/(1-s)` is realised by
homogenising (`Polynomial.homogenize`) and evaluating at `(s, 1 - s)`; it turns a relation into an
identity `Y + W (c + (1-c) s)^k = s^k Ã`, to which a Rolle-type argument (the `(d+1)`-st
derivative kills `Y`) is applied; the second factor vanishes at `s = c/(c-1) ≠ 0`.
-/

open Polynomial

namespace GenK

noncomputable section

/-- `(P, Z)` is a relation for the exponent `k` and the shift `c`. -/
def IsRel (c : ℚ) (k : ℕ) (P Z : ℚ[X]) : Prop := X ^ k ∣ P * (X + 1) ^ k + Z * (X + C c) ^ k

/-! ### The substitution `x = s / (1 - s)` -/

/-- `φ = (s, 1 - s)` -/
def φ : Fin 2 → ℚ[X] := ![X, 1 - X]

/-- `hz p n = (1 - s)^n p(s / (1 - s))`, a polynomial in `s` when `natDegree p ≤ n`. -/
def hz (p : ℚ[X]) (n : ℕ) : ℚ[X] := MvPolynomial.aeval φ (p.homogenize n)

theorem hz_add (p q : ℚ[X]) (n : ℕ) : hz (p + q) n = hz p n + hz q n := by
  simp [hz, homogenize_add]

theorem hz_mul (p q : ℚ[X]) {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) :
    hz (p * q) (m + n) = hz p m * hz q n := by
  simp [hz, homogenize_mul p q hm hn]

theorem hz_X_add_C_pow (c : ℚ) (k : ℕ) :
    hz ((X + C c) ^ k) k = (X + C c * (1 - X)) ^ k := by
  have h : ((X + C c) ^ k).homogenize k = (MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1) ^ k := by
    apply homogenize_eq_of_isHomogeneous
    · have h1 : (MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ).IsHomogeneous 1 :=
        MvPolynomial.IsHomogeneous.add (MvPolynomial.isHomogeneous_X _ _)
          (by simpa using (MvPolynomial.isHomogeneous_C_mul_X c 1))
      simpa using h1.pow k
    · simp
  simp [hz, h, φ]

theorem hz_X_pow (k : ℕ) : hz (X ^ k) k = X ^ k := by
  simp [hz, homogenize_X_pow (le_refl k), φ]

/-- `hz p n` evaluated at `s ≠ 1` is `(1 - s)^n p(s/(1-s))`. -/
theorem eval_hz {p : ℚ[X]} {n : ℕ} (hn : p.natDegree ≤ n) (s : ℚ) (hs : s ≠ 1) :
    (hz p n).eval s = p.eval (s / (1 - s)) * (1 - s) ^ n := by
  have h1 : (1 : ℚ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have : (hz p n).eval s = MvPolynomial.eval ![s, 1 - s] (p.homogenize n) := by
    simp only [hz]
    induction p.homogenize n using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, eval_mul, hp, MvPolynomial.eval_X]
      fin_cases i <;> simp [φ]
  rw [this, eval_homogenize hn _ (by simpa using h1)]
  simp

theorem hz_eq_zero {p : ℚ[X]} {n : ℕ} (hn : p.natDegree ≤ n) (h : hz p n = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_not_bddAbove
  intro ⟨B, hB⟩
  -- every t ≥ 0 is a root
  have hroot : ∀ t : ℚ, 0 ≤ t → p.IsRoot t := by
    intro t ht
    have hs : t / (1 + t) ≠ 1 := by
      intro he
      have h1 : (1 : ℚ) + t ≠ 0 := by linarith
      field_simp at he; linarith
    have := eval_hz hn (t / (1 + t)) hs
    rw [h, eval_zero] at this
    have h1 : (1 : ℚ) + t ≠ 0 := by linarith
    have e : t / (1 + t) / (1 - t / (1 + t)) = t := by field_simp; ring
    have e2 : (1 : ℚ) - t / (1 + t) ≠ 0 := by
      rw [sub_ne_zero]; intro he; field_simp at he; linarith
    rw [e] at this
    exact (mul_eq_zero.mp this.symm).resolve_right (pow_ne_zero _ e2)
  have := hB (hroot (|B| + 1) (by positivity))
  linarith [le_abs_self B]

theorem natDegree_hz_le (p : ℚ[X]) (n : ℕ) : (hz p n).natDegree ≤ n := by
  simp only [hz, homogenize, map_sum, MvPolynomial.aeval_monomial]
  apply natDegree_sum_le_of_forall_le
  intro kl hkl
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  have e0 : (fun₀ | 0 => kl.1 | 1 => kl.2 : Fin 2 →₀ ℕ) 0 = kl.1 := by simp
  have e1 : (fun₀ | 0 => kl.1 | 1 => kl.2 : Fin 2 →₀ ℕ) 1 = kl.2 := by simp
  simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, e0, e1]
  rw [← C_eq_algebraMap]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_mul_le).trans ?_
  have h1 : (1 - X : ℚ[X]).natDegree ≤ 1 := by
    rw [sub_eq_add_neg]; exact (natDegree_add_le _ _).trans (by simp)
  have := natDegree_pow_le_of_le kl.2 h1
  have h2 := natDegree_X_pow_le (R := ℚ) kl.1
  omega

/-! ### The Rolle-type argument -/

theorem natDegree_lt_of_iterate_derivative_eq_zero {f : ℚ[X]} {m : ℕ}
    (h : derivative^[m] f = 0) : f.natDegree < m ∨ f = 0 := by
  by_cases hf : f = 0
  · exact Or.inr hf
  left
  by_contra hge
  push Not at hge
  have hc : (derivative^[m] f).coeff (f.natDegree - m) = 0 := by rw [h]; simp
  rw [coeff_iterate_derivative, Nat.sub_add_cancel hge] at hc
  have hlc : f.coeff f.natDegree ≠ 0 := by simpa using hf
  rw [nsmul_eq_mul] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · have : (f.natDegree.descFactorial m : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hge).ne'
    exact this h1
  · exact hlc h1

/-- the linear factor `c + (1 - c) s` -/
def lin (c : ℚ) : ℚ[X] := C c + C (1 - c) * X

theorem lin_eq {c : ℚ} (hc1 : c ≠ 1) : lin c = C (1 - c) * (X - C (c / (c - 1))) := by
  have h : (c - 1) ≠ 0 := sub_ne_zero.mpr hc1
  have e : (1 - c) * (c / (c - 1)) = -c := by field_simp; ring
  rw [lin, mul_sub, ← C_mul, e, C_neg]; ring

theorem natDeg_lin_pow {c : ℚ} (hc1 : c ≠ 1) (k : ℕ) : ((lin c) ^ k).natDegree = k := by
  have h : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  rw [lin_eq hc1, mul_pow, ← C_pow, natDegree_C_mul (pow_ne_zero _ h), natDegree_pow,
    natDegree_X_sub_C]; ring

theorem lin_pow_ne_zero {c : ℚ} (hc1 : c ≠ 1) (k : ℕ) : (lin c) ^ k ≠ 0 := by
  have h : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  rw [lin_eq hc1]
  exact pow_ne_zero _ (mul_ne_zero (C_ne_zero.mpr h) (X_sub_C_ne_zero _))

theorem rolle_core {c : ℚ} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {k d : ℕ} (hd : 2 * d + 2 ≤ k)
    {Y W A : ℚ[X]} (hY : Y.natDegree ≤ d) (hW : W.natDegree ≤ d)
    (h : Y + W * (lin c) ^ k = X ^ k * A) : W = 0 ∧ Y = 0 := by
  set m := d + 1
  set s0 := c / (c - 1) with hs0def
  have hs0 : s0 ≠ 0 := div_ne_zero hc0 (sub_ne_zero.mpr hc1)
  have e0 : derivative^[m] Y = 0 := iterate_derivative_eq_zero (by omega)
  have hH : derivative^[m] (W * (lin c) ^ k) = derivative^[m] (X ^ k * A) := by
    have := congrArg (derivative^[m]) h
    rwa [iterate_map_add, e0, zero_add] at this
  set H := derivative^[m] (W * (lin c) ^ k) with hHdef
  have d1 : X ^ (k - m) ∣ H := by
    rw [hH]; exact pow_sub_dvd_iterate_derivative_of_pow_dvd m (dvd_mul_right _ _)
  have d2 : (X - C s0) ^ (k - m) ∣ H := by
    apply pow_sub_dvd_iterate_derivative_of_pow_dvd m
    rw [lin_eq hc1, mul_pow]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have cop : IsCoprime (X ^ (k - m) : ℚ[X]) ((X - C s0) ^ (k - m)) := by
    apply IsCoprime.pow
    have := isCoprime_X_sub_C_of_isUnit_sub (R := ℚ) (a := 0) (b := s0)
      (by simpa using (neg_ne_zero.mpr hs0).isUnit)
    simpa using this
  have d3 := cop.mul_dvd d1 d2
  have hdegH : H.natDegree ≤ k - 1 := by
    refine (natDegree_iterate_derivative _ _).trans ?_
    have : (W * (lin c) ^ k).natDegree ≤ d + k :=
      natDegree_mul_le.trans (add_le_add hW (natDeg_lin_pow hc1 k).le)
    omega
  have hH0 : H = 0 := by
    by_contra hne
    have := natDegree_le_of_dvd d3 hne
    rw [(monic_X_pow _).natDegree_mul ((monic_X_sub_C s0).pow _), natDegree_X_pow, natDegree_pow,
      natDegree_X_sub_C] at this
    omega
  have hW0 : W = 0 := by
    by_contra hWne
    rcases natDegree_lt_of_iterate_derivative_eq_zero (hHdef ▸ hH0) with hlt | hz0
    · rw [natDegree_mul hWne (lin_pow_ne_zero hc1 k), natDeg_lin_pow hc1] at hlt
      omega
    · rcases mul_eq_zero.mp hz0 with h1 | h1
      · exact hWne h1
      · exact lin_pow_ne_zero hc1 k h1
  refine ⟨hW0, ?_⟩
  rw [hW0, zero_mul, add_zero] at h
  by_contra hYne
  have hA : A ≠ 0 := by rintro rfl; simp at h; exact hYne h
  have : Y.natDegree = k + A.natDegree := by rw [h, natDegree_mul (pow_ne_zero _ X_ne_zero) hA, natDegree_X_pow]
  omega

/-! ### Proposition 3.1(b): normality -/

theorem natDegree_U_le (c : ℚ) (k : ℕ) : ((X + C c : ℚ[X]) ^ k).natDegree ≤ k := by
  have h1 : (X + C c : ℚ[X]).natDegree ≤ 1 := (natDegree_add_le (X : ℚ[X]) (C c)).trans (by simp)
  exact (natDegree_pow_le_of_le k h1).trans (by simp)

theorem normality {c : ℚ} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {k d : ℕ} (hd : 2 * d + 2 ≤ k)
    {P Z : ℚ[X]} (hP : P.natDegree ≤ d) (hZ : Z.natDegree ≤ d) (hrel : IsRel c k P Z) :
    P = 0 ∧ Z = 0 := by
  obtain ⟨A, hA⟩ := hrel
  have hU : ((X + 1 : ℚ[X]) ^ k) = (X + C 1) ^ k := by rw [C_1]
  rw [hU] at hA
  have hAdeg : A.natDegree ≤ d := by
    by_cases hA0 : A = 0
    · simp [hA0]
    have hle : (P * (X + C 1) ^ k + Z * (X + C c) ^ k).natDegree ≤ d + k :=
      (natDegree_add_le _ _).trans (max_le (natDegree_mul_le.trans (add_le_add hP (natDegree_U_le 1 k)))
        (natDegree_mul_le.trans (add_le_add hZ (natDegree_U_le c k))))
    rw [hA, natDegree_mul (pow_ne_zero _ X_ne_zero) hA0, natDegree_X_pow] at hle
    omega
  have key : hz P d + hz Z d * (lin c) ^ k = X ^ k * hz A d := by
    have h1 : hz (P * (X + C 1) ^ k + Z * (X + C c) ^ k) (d + k) = hz (X ^ k * A) (d + k) := by
      rw [hA]
    rw [hz_add, hz_mul P _ hP (natDegree_U_le 1 k), hz_mul Z _ hZ (natDegree_U_le c k),
      hz_X_add_C_pow, hz_X_add_C_pow, show d + k = k + d by ring,
      hz_mul (X ^ k) A (natDegree_X_pow_le k) hAdeg, hz_X_pow] at h1
    have e1 : (X + C (1 : ℚ) * (1 - X)) = 1 := by simp
    have e2 : (X + C c * (1 - X)) = lin c := by rw [lin, C_sub, C_1]; ring
    rw [e1, e2, one_pow, mul_one] at h1
    exact h1
  obtain ⟨hW, hY⟩ := rolle_core hc0 hc1 hd (natDegree_hz_le P d) (natDegree_hz_le Z d) key
  exact ⟨hz_eq_zero hP hY, hz_eq_zero hZ hW⟩

/-! ### Proposition 3.1(a): existence -/

/-- The linear map `(P, Z) ↦ (coefficients 0, …, k-1 of P (X+1)^k + Z (X+c)^k)`. -/
def relMap (c : ℚ) (k d : ℕ) : (degreeLT ℚ (d + 1) × degreeLT ℚ (d + 1)) →ₗ[ℚ] (Fin k → ℚ) where
  toFun pz := fun i => ((pz.1 : ℚ[X]) * (X + 1) ^ k + (pz.2 : ℚ[X]) * (X + C c) ^ k).coeff i
  map_add' x y := by
    ext i; simp [add_mul]; ring
  map_smul' a x := by
    ext i; simp [smul_eq_C_mul, mul_assoc, ← mul_add, coeff_C_mul]

theorem exists_rel (c : ℚ) (k d : ℕ) (hd : k < 2 * d + 2) :
    ∃ P Z : ℚ[X], (P ≠ 0 ∨ Z ≠ 0) ∧ P.natDegree ≤ d ∧ Z.natDegree ≤ d ∧ IsRel c k P Z := by
  have hfin : Module.finrank ℚ (Fin k → ℚ) < Module.finrank ℚ (degreeLT ℚ (d + 1) × degreeLT ℚ (d + 1)) := by
    rw [Module.finrank_prod, (degreeLTEquiv ℚ (d + 1)).finrank_eq, Module.finrank_fin_fun,
      Module.finrank_fin_fun]
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt hfin)
  refine ⟨v.1, v.2, ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hv0
    exact Prod.ext (Subtype.ext hcon.1) (Subtype.ext hcon.2)
  · have := v.1.2; rw [mem_degreeLT] at this
    exact natDegree_le_of_degree_le (Order.lt_succ_iff.mp (by exact_mod_cast this))
  · have := v.2.2; rw [mem_degreeLT] at this
    exact natDegree_le_of_degree_le (Order.lt_succ_iff.mp (by exact_mod_cast this))
  · rw [IsRel, X_pow_dvd_iff]
    intro i hi
    have h0 : relMap c k d v = 0 := LinearMap.mem_ker.mp hv
    have := congrFun h0 ⟨i, hi⟩
    simp only [relMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    simpa using this

end

end GenK
