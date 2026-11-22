import Frobenius.GenKBasis

/-!
# The relation lattice (Lemma 3.3, Proposition 4.1, Theorems 1.2 and 4.2)

For natural numbers `0 < p < q` let
`L = {(i, j) ∈ ℤ² : n^k ∣ i (n+p)^k + j (n+q)^k}`, the relation lattice of
`⟨n^k, (n+p)^k, (n+q)^k⟩`; the consecutive case is `(p, q) = (1, 2)`.  We work with the sup norm
`‖(i, j)‖ = max |i| |j|` (`supn`).  The Euclidean statements of the paper follow up to factors `√2`.
The polynomial relations for `(x+p, x+q)` are obtained from those for `(x+1, x+q/p)` of
`GenKBasis` by the substitution `x = p y` (`transfer`).
-/

open Polynomial

namespace GenK

noncomputable section

variable {p q : ℕ}

/-- membership in the relation lattice of `⟨n^k, (n+p)^k, (n+q)^k⟩` -/
def InL (p q k n : ℕ) (u : ℤ × ℤ) : Prop :=
  ((n : ℤ) ^ k) ∣ u.1 * ((n : ℤ) + p) ^ k + u.2 * ((n : ℤ) + q) ^ k

/-- sup norm -/
def supn (u : ℤ × ℤ) : ℕ := max u.1.natAbs u.2.natAbs

/-- determinant of integer vectors -/
def detZ (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - v.1 * u.2

theorem InL.add {k n : ℕ} {u v : ℤ × ℤ} (hu : InL p q k n u) (hv : InL p q k n v) :
    InL p q k n (u + v) := by
  unfold InL at *; simp only [Prod.fst_add, Prod.snd_add]
  have := dvd_add hu hv; convert this using 1; ring

theorem InL.smul {k n : ℕ} {u : ℤ × ℤ} (m : ℤ) (hu : InL p q k n u) : InL p q k n (m • u) := by
  unfold InL at *; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have := dvd_mul_of_dvd_right hu m; convert this using 1; ring

/-- If `gcd(n, p, q) = 1` then `1` is a combination of `n^k`, `(n+p)^k`, `(n+q)^k`. -/
theorem bezout3 {k n : ℕ} (hg : Nat.gcd n (Nat.gcd p q) = 1) :
    ∃ x y z : ℤ, x * (n : ℤ) ^ k + y * ((n : ℤ) + p) ^ k + z * ((n : ℤ) + q) ^ k = 1 := by
  obtain ⟨α, β, γ, h⟩ : ∃ α β γ : ℤ, α * n + β * p + γ * q = 1 := by
    have h1 := Nat.gcd_eq_gcd_ab n (Nat.gcd p q)
    have h2 := Nat.gcd_eq_gcd_ab p q
    rw [hg] at h1
    set A := n.gcdA (Nat.gcd p q)
    set B := n.gcdB (Nat.gcd p q)
    refine ⟨A, B * p.gcdA q, B * p.gcdB q, ?_⟩
    push_cast at h1
    linear_combination -h1 - B * h2
  have hs : Ideal.span ({(n : ℤ), (n : ℤ) + p, (n : ℤ) + q} : Set ℤ) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e : (1 : ℤ) = (α - β - γ) * n + β * ((n : ℤ) + p) + γ * ((n : ℤ) + q) := by
      linear_combination -h
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have hk := Ideal.span_pow_eq_top _ hs k
  simp only [Set.image_insert_eq, Set.image_singleton] at hk
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_insert] at hk
  obtain ⟨x, w, hw, hx⟩ := hk
  rw [Ideal.mem_span_pair] at hw
  obtain ⟨y, z, hyz⟩ := hw
  exact ⟨x, y, z, by rw [hx, ← hyz]; ring⟩

/-- The determinant of two vectors of the lattice is divisible by its index `n^k`. -/
theorem dvd_detZ {k n : ℕ} (hg : Nat.gcd n (Nat.gcd p q) = 1) {u v : ℤ × ℤ}
    (hu : InL p q k n u) (hv : InL p q k n v) : ((n : ℤ) ^ k) ∣ detZ u v := by
  obtain ⟨x, y, z, hxyz⟩ := bezout3 (k := k) hg
  have e1 : detZ u v * ((n : ℤ) + p) ^ k =
      v.2 * (u.1 * ((n : ℤ) + p) ^ k + u.2 * ((n : ℤ) + q) ^ k) -
        u.2 * (v.1 * ((n : ℤ) + p) ^ k + v.2 * ((n : ℤ) + q) ^ k) := by
    simp only [detZ]; ring
  have e2 : detZ u v * ((n : ℤ) + q) ^ k =
      u.1 * (v.1 * ((n : ℤ) + p) ^ k + v.2 * ((n : ℤ) + q) ^ k) -
        v.1 * (u.1 * ((n : ℤ) + p) ^ k + u.2 * ((n : ℤ) + q) ^ k) := by
    simp only [detZ]; ring
  have d1 : ((n : ℤ) ^ k) ∣ detZ u v * ((n : ℤ) + p) ^ k := by
    rw [e1]; exact dvd_sub (dvd_mul_of_dvd_right hu _) (dvd_mul_of_dvd_right hv _)
  have d2 : ((n : ℤ) ^ k) ∣ detZ u v * ((n : ℤ) + q) ^ k := by
    rw [e2]; exact dvd_sub (dvd_mul_of_dvd_right hv _) (dvd_mul_of_dvd_right hu _)
  have e : detZ u v = x * (n : ℤ) ^ k * detZ u v + y * (detZ u v * ((n : ℤ) + p) ^ k) +
      z * (detZ u v * ((n : ℤ) + q) ^ k) := by
    linear_combination (-(detZ u v)) * hxyz
  rw [e]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (dvd_mul_of_dvd_right d1 _))
    (dvd_mul_of_dvd_right d2 _)

theorem abs_detZ_le (u v : ℤ × ℤ) : (detZ u v).natAbs ≤ 2 * supn u * supn v := by
  simp only [detZ, supn]
  have h1 : (u.1 * v.2 - v.1 * u.2).natAbs ≤ (u.1 * v.2).natAbs + (v.1 * u.2).natAbs :=
    Int.natAbs_sub_le _ _
  rw [Int.natAbs_mul, Int.natAbs_mul] at h1
  have a1 : u.1.natAbs ≤ max u.1.natAbs u.2.natAbs := le_max_left _ _
  have a2 : u.2.natAbs ≤ max u.1.natAbs u.2.natAbs := le_max_right _ _
  have b1 : v.1.natAbs ≤ max v.1.natAbs v.2.natAbs := le_max_left _ _
  have b2 : v.2.natAbs ≤ max v.1.natAbs v.2.natAbs := le_max_right _ _
  have := Nat.mul_le_mul a1 b2
  have := Nat.mul_le_mul b1 a2
  nlinarith

/-- Cramer: `det(v₁,v₂) u = det(u,v₂) v₁ - det(u,v₁) v₂`. -/
theorem cramer (u v1 v2 : ℤ × ℤ) :
    detZ v1 v2 • u = detZ u v2 • v1 - detZ u v1 • v2 := by
  ext <;> simp only [detZ, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul] <;> ring

/-! ### Integer versions of the polynomial relations -/

/-- A rational polynomial vector has an integer multiple. -/
theorem exists_int_vec (V : ℚ[X] × ℚ[X]) :
    ∃ (D : ℤ) (p z : ℤ[X]), D ≠ 0 ∧ p.map (Int.castRingHom ℚ) = C (D : ℚ) * V.1 ∧
      z.map (Int.castRingHom ℚ) = C (D : ℚ) * V.2 := by
  obtain ⟨b1, hb1, h1⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) V.1
  obtain ⟨b2, hb2, h2⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) V.2
  have b1ne : b1 ≠ 0 := nonZeroDivisors.ne_zero hb1
  have b2ne : b2 ≠ 0 := nonZeroDivisors.ne_zero hb2
  have e1 : (IsLocalization.integerNormalization (nonZeroDivisors ℤ) V.1).map (Int.castRingHom ℚ) =
      C (b1 : ℚ) * V.1 := by
    rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, h1, zsmul_eq_mul, C_eq_intCast]
  have e2 : (IsLocalization.integerNormalization (nonZeroDivisors ℤ) V.2).map (Int.castRingHom ℚ) =
      C (b2 : ℚ) * V.2 := by
    rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, h2, zsmul_eq_mul, C_eq_intCast]
  refine ⟨b1 * b2, C b2 * IsLocalization.integerNormalization (nonZeroDivisors ℤ) V.1,
    C b1 * IsLocalization.integerNormalization (nonZeroDivisors ℤ) V.2, mul_ne_zero b1ne b2ne, ?_, ?_⟩
  · rw [Polynomial.map_mul, map_C, e1, eq_intCast, Int.cast_mul, C_mul]; ring
  · rw [Polynomial.map_mul, map_C, e2, eq_intCast, Int.cast_mul, C_mul]; ring

theorem X_pow_dvd_of_map {k : ℕ} {f : ℤ[X]} (h : X ^ k ∣ f.map (Int.castRingHom ℚ)) :
    X ^ k ∣ f := by
  rw [X_pow_dvd_iff] at h ⊢
  intro d hd
  have := h d hd
  rw [coeff_map, eq_intCast, Int.cast_eq_zero] at this
  exact this

/-- bound on `|p(n)|` -/
def cb (p : ℤ[X]) (d : ℕ) : ℕ := ∑ i ∈ Finset.range (d + 1), (p.coeff i).natAbs

theorem natAbs_eval_le {p : ℤ[X]} {d : ℕ} (hp : p.natDegree ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    (p.eval (n : ℤ)).natAbs ≤ cb p d * n ^ d := by
  rw [eval_eq_sum_range' (by omega : p.natDegree < d + 1)]
  refine (Int.natAbs_sum_le _ _).trans ?_
  rw [cb, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn (by simp at hi; omega))

/-! ### The substitution `x = p y` -/

/-- `(P, Z)` is a relation for `(x+p, x+q)`. -/
def IsRelPQ (p q : ℚ) (k : ℕ) (P Z : ℚ[X]) : Prop :=
  X ^ k ∣ P * (X + C p) ^ k + Z * (X + C q) ^ k

theorem transfer {p q : ℚ} (hp : p ≠ 0) {k : ℕ} {P Z : ℚ[X]} (h : IsRel (q / p) k P Z) :
    IsRelPQ p q k (P.comp (C p⁻¹ * X)) (Z.comp (C p⁻¹ * X)) := by
  obtain ⟨A, hA⟩ := h
  set σ : ℚ[X] := C p⁻¹ * X with hσ
  have hpp : C p * C p⁻¹ = (1 : ℚ[X]) := by rw [← C_mul, mul_inv_cancel₀ hp, C_1]
  have hq' : C p * C (q / p) = C q := by rw [← C_mul]; congr 1; field_simp
  have e1 : (X + C p : ℚ[X]) = C p * (σ + 1) := by rw [hσ]; linear_combination (-X) * hpp
  have e2 : (X + C q : ℚ[X]) = C p * (σ + C (q / p)) := by
    rw [hσ]; linear_combination (-X) * hpp - hq'
  have e3 : (X : ℚ[X]) = C p * σ := by rw [hσ]; linear_combination (-X) * hpp
  have hc := congrArg (fun f => f.comp σ) hA
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, one_comp] at hc
  refine ⟨A.comp σ, ?_⟩
  calc P.comp σ * (X + C p) ^ k + Z.comp σ * (X + C q) ^ k
      = (C p) ^ k * (P.comp σ * (σ + 1) ^ k + Z.comp σ * (σ + C (q / p)) ^ k) := by
        rw [e1, e2, mul_pow, mul_pow]; ring
    _ = (C p) ^ k * (σ ^ k * A.comp σ) := by rw [hc]
    _ = (C p * σ) ^ k * A.comp σ := by ring
    _ = X ^ k * A.comp σ := by rw [← e3]

theorem natDegree_comp_sigma {p : ℚ} (hp : p ≠ 0) (P : ℚ[X]) :
    (P.comp (C p⁻¹ * X)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero hp), mul_one]

/-- **Proposition 3.1(c)** for `(x+p, x+q)`. -/
theorem exists_basisPQ (p q : ℚ) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) (k : ℕ) (hk : 2 ≤ k) :
    ∃ V1 V2 : ℚ[X] × ℚ[X],
      (IsRelPQ p q k V1.1 V1.2 ∧ V1.1.natDegree ≤ k / 2 ∧ V1.2.natDegree ≤ k / 2) ∧
      (IsRelPQ p q k V2.1 V2.2 ∧ V2.1.natDegree ≤ (k + 1) / 2 ∧ V2.2.natDegree ≤ (k + 1) / 2) ∧
      ∃ κ : ℚ, κ ≠ 0 ∧ det2 V1 V2 = C κ * X ^ k := by
  have hc0 : q / p ≠ 0 := div_ne_zero hq hp
  have hc1 : q / p ≠ 1 := fun h => hpq ((div_eq_one_iff_eq hp).mp h).symm
  obtain ⟨V1, V2, hV1, hV2, κ, hκ, hdet⟩ := exists_basis (q / p) hc0 hc1 k hk
  set σ : ℚ[X] := C p⁻¹ * X with hσ
  refine ⟨(V1.1.comp σ, V1.2.comp σ), (V2.1.comp σ, V2.2.comp σ),
    ⟨transfer hp hV1.1, ?_, ?_⟩, ⟨transfer hp hV2.1, ?_, ?_⟩, κ * p⁻¹ ^ k, ?_, ?_⟩
  · rw [natDegree_comp_sigma hp]; exact hV1.2.1
  · rw [natDegree_comp_sigma hp]; exact hV1.2.2
  · rw [natDegree_comp_sigma hp]; exact hV2.2.1
  · rw [natDegree_comp_sigma hp]; exact hV2.2.2
  · exact mul_ne_zero hκ (pow_ne_zero _ (inv_ne_zero hp))
  · have h := congrArg (fun f => f.comp σ) hdet
    simp only [det2, sub_comp, mul_comp, C_comp, pow_comp, X_comp] at h
    simp only [det2]
    rw [h, hσ, mul_pow, ← C_pow, C_mul]; ring

/-- The data of Lemma 3.3: integer relation vectors `(p₁, z₁)`, `(p₂, z₂)` of degrees
`≤ ⌊k/2⌋`, `≤ ⌈k/2⌉` with `p₁ z₂ - p₂ z₁ = K X^k`, `K ≠ 0`. -/
structure IntBasis (p q k : ℕ) where
  p1 : ℤ[X]
  z1 : ℤ[X]
  p2 : ℤ[X]
  z2 : ℤ[X]
  K : ℤ
  hK : K ≠ 0
  rel1 : X ^ k ∣ p1 * (X + C (p : ℤ)) ^ k + z1 * (X + C (q : ℤ)) ^ k
  rel2 : X ^ k ∣ p2 * (X + C (p : ℤ)) ^ k + z2 * (X + C (q : ℤ)) ^ k
  dp1 : p1.natDegree ≤ k / 2
  dz1 : z1.natDegree ≤ k / 2
  dp2 : p2.natDegree ≤ (k + 1) / 2
  dz2 : z2.natDegree ≤ (k + 1) / 2
  det : p1 * z2 - p2 * z1 = C K * X ^ k

theorem natDegree_map_le' {p : ℚ[X]} {f : ℤ[X]} {D : ℤ} (_hD : D ≠ 0) {e : ℕ}
    (h : f.map (Int.castRingHom ℚ) = C (D : ℚ) * p) (hp : p.natDegree ≤ e) : f.natDegree ≤ e := by
  have h1 : (f.map (Int.castRingHom ℚ)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (RingHom.injective_int _) _
  rw [← h1, h]
  exact (natDegree_C_mul_le _ _).trans hp

theorem rel_int {k : ℕ} {V : ℚ[X] × ℚ[X]} (hV : IsRelPQ (p : ℚ) (q : ℚ) k V.1 V.2) {D : ℤ}
    {f z : ℤ[X]} (hf : f.map (Int.castRingHom ℚ) = C (D : ℚ) * V.1)
    (hz : z.map (Int.castRingHom ℚ) = C (D : ℚ) * V.2) :
    X ^ k ∣ f * (X + C (p : ℤ)) ^ k + z * (X + C (q : ℤ)) ^ k := by
  apply X_pow_dvd_of_map
  have hpm : (X + C (p : ℤ) : ℤ[X]).map (Int.castRingHom ℚ) = X + C (p : ℚ) := by
    rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]; simp
  have hqm : (X + C (q : ℤ) : ℤ[X]).map (Int.castRingHom ℚ) = X + C (q : ℚ) := by
    rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]; simp
  have : (f * (X + C (p : ℤ)) ^ k + z * (X + C (q : ℤ)) ^ k).map (Int.castRingHom ℚ) =
      C (D : ℚ) * (V.1 * (X + C (p : ℚ)) ^ k + V.2 * (X + C (q : ℚ)) ^ k) := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, hpm, hqm, hf, hz]
    ring
  rw [this]; exact dvd_mul_of_dvd_right hV _

/-- **Lemma 3.3** (existence of the integer basis). -/
theorem exists_intBasis (hp : 0 < p) (hpq : p < q) (k : ℕ) (hk : 2 ≤ k) :
    Nonempty (IntBasis p q k) := by
  obtain ⟨V1, V2, hV1, hV2, κ, hκ, hdet⟩ := exists_basisPQ (p : ℚ) (q : ℚ)
    (by exact_mod_cast hp.ne') (by exact_mod_cast (hp.trans hpq).ne') (by exact_mod_cast hpq.ne) k hk
  obtain ⟨D1, p1, z1, hD1, hp1, hz1⟩ := exists_int_vec V1
  obtain ⟨D2, p2, z2, hD2, hp2, hz2⟩ := exists_int_vec V2
  have hmap : (p1 * z2 - p2 * z1).map (Int.castRingHom ℚ) = C ((D1 * D2 : ℤ) * κ : ℚ) * X ^ k := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, hp1, hz1, hp2, hz2]
    have : V1.1 * V2.2 - V2.1 * V1.2 = C κ * X ^ k := hdet
    rw [show C (D1 : ℚ) * V1.1 * (C (D2 : ℚ) * V2.2) - C (D2 : ℚ) * V2.1 * (C (D1 : ℚ) * V1.2)
        = C ((D1 : ℚ) * D2) * (V1.1 * V2.2 - V2.1 * V1.2) by simp only [C_mul]; ring, this]
    push_cast; simp only [C_mul]; ring
  set f := p1 * z2 - p2 * z1
  set K := f.coeff k
  have hcoef : ∀ i, ((f.coeff i : ℤ) : ℚ) = if i = k then (D1 * D2 : ℤ) * κ else 0 := by
    intro i
    have := congrArg (fun g => g.coeff i) hmap
    simp only [coeff_map, coeff_C_mul, coeff_X_pow] at this
    rw [eq_intCast] at this
    simpa [mul_ite] using this
  have hK : (K : ℚ) = (D1 * D2 : ℤ) * κ := by simpa using hcoef k
  refine ⟨⟨p1, z1, p2, z2, K, ?_, rel_int hV1.1 hp1 hz1, rel_int hV2.1 hp2 hz2,
    natDegree_map_le' hD1 hp1 hV1.2.1, natDegree_map_le' hD1 hz1 hV1.2.2,
    natDegree_map_le' hD2 hp2 hV2.2.1, natDegree_map_le' hD2 hz2 hV2.2.2, ?_⟩⟩
  · intro h0
    rw [h0] at hK
    push_cast at hK
    rcases mul_eq_zero.mp hK.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hD1 (by exact_mod_cast h')
      · exact hD2 (by exact_mod_cast h')
    · exact hκ h
  · ext i
    rw [coeff_C_mul, coeff_X_pow]
    by_cases hi : i = k
    · subst hi; simp [K, f]
    · simp only [hi, ↓reduceIte, mul_zero]
      have := hcoef i
      simp only [hi, ↓reduceIte] at this
      exact_mod_cast this

/-- the lattice vectors `v_t(n)` -/
def vec (p z : ℤ[X]) (n : ℕ) : ℤ × ℤ := (p.eval (n : ℤ), z.eval (n : ℤ))

theorem vec_inL {k : ℕ} {f z : ℤ[X]}
    (h : X ^ k ∣ f * (X + C (p : ℤ)) ^ k + z * (X + C (q : ℤ)) ^ k) (n : ℕ) :
    InL p q k n (vec f z n) := by
  obtain ⟨g, hg⟩ := h
  have := congrArg (eval (n : ℤ)) hg
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at this
  exact ⟨g.eval (n : ℤ), by simp only [vec]; rw [this]⟩

theorem detZ_vec {k : ℕ} (B : IntBasis p q k) (n : ℕ) :
    detZ (vec B.p1 B.z1 n) (vec B.p2 B.z2 n) = B.K * (n : ℤ) ^ k := by
  have := congrArg (eval (n : ℤ)) B.det
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at this
  simp only [detZ, vec]; linarith

theorem supn_vec_le {p z : ℤ[X]} {d : ℕ} (hp : p.natDegree ≤ d) (hz : z.natDegree ≤ d) {n : ℕ}
    (hn : 1 ≤ n) : supn (vec p z n) ≤ (cb p d + cb z d) * n ^ d := by
  simp only [supn, vec]
  have h1 := natAbs_eval_le hp hn
  have h2 := natAbs_eval_le hz hn
  rw [add_mul]
  exact max_le (h1.trans (Nat.le_add_right _ _)) (h2.trans (Nat.le_add_left _ _))

/-- **Proposition 4.1 / Theorem 1.2** (sup-norm version). With `d₁ = ⌊k/2⌋`, `d₂ = ⌈k/2⌉`:
* `L_n^k` has a nonzero vector of norm `≤ Γ n^{d₁}`, and every nonzero vector has
  norm `≥ n^{d₁} / γ` (first minimum);
* `L_n^k` has two independent vectors of norm `≤ Γ n^{d₂}`, and any two independent vectors
  have maximal norm `≥ n^{d₂} / γ` (second minimum). -/
theorem lattice_minima (hp : 0 < p) (hpq : p < q) (k : ℕ) (hk : 2 ≤ k) :
    ∃ γ Γ : ℕ, 0 < γ ∧ ∀ n : ℕ, 1 ≤ n → Nat.gcd n (Nat.gcd p q) = 1 →
      (∃ u, InL p q k n u ∧ u ≠ 0 ∧ supn u ≤ Γ * n ^ (k / 2)) ∧
      (∀ u, InL p q k n u → u ≠ 0 → n ^ (k / 2) ≤ γ * supn u) ∧
      (∃ u v, InL p q k n u ∧ InL p q k n v ∧ detZ u v ≠ 0 ∧ supn u ≤ Γ * n ^ ((k + 1) / 2) ∧
        supn v ≤ Γ * n ^ ((k + 1) / 2)) ∧
      (∀ u v, InL p q k n u → InL p q k n v → detZ u v ≠ 0 →
        n ^ ((k + 1) / 2) ≤ γ * max (supn u) (supn v)) := by
  obtain ⟨B⟩ := exists_intBasis hp hpq k hk
  set d1 := k / 2
  set d2 := (k + 1) / 2
  have hsum : d1 + d2 = k := by omega
  have hd12 : d1 ≤ d2 := by omega
  set C1 := cb B.p1 d1 + cb B.z1 d1 with hC1
  set C2 := cb B.p2 d2 + cb B.z2 d2 with hC2
  have hdp1 : B.p1.natDegree ≤ d2 := B.dp1.trans hd12
  have hdz1 : B.z1.natDegree ≤ d2 := B.dz1.trans hd12
  set C1' := cb B.p1 d2 + cb B.z1 d2 with hC1'
  refine ⟨2 * (C1 + C1' + C2 + 1), C1 + C1' + C2 + 1, by omega, fun n hn hg => ?_⟩
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn
  have hdetv : detZ (vec B.p1 B.z1 n) (vec B.p2 B.z2 n) ≠ 0 := by
    rw [detZ_vec]; exact mul_ne_zero B.hK (pow_ne_zero _ hnpos.ne')
  have hv1 := vec_inL B.rel1 n
  have hv2 := vec_inL B.rel2 n
  have hv1ne : vec B.p1 B.z1 n ≠ 0 := by
    intro h; apply hdetv; rw [h]; simp [detZ]
  have hs1 := supn_vec_le B.dp1 B.dz1 hn
  have hs1' := supn_vec_le hdp1 hdz1 hn
  have hs2 := supn_vec_le B.dp2 B.dz2 hn
  have hnk : (n : ℕ) ^ k = n ^ d1 * n ^ d2 := by rw [← pow_add, hsum]
  have hpos1 : 0 < n ^ d1 := pow_pos hn _
  have hpos2 : 0 < n ^ d2 := pow_pos hn _
  -- key: a nonzero multiple of n^k has absolute value ≥ n^k
  have big : ∀ x : ℤ, ((n : ℤ) ^ k) ∣ x → x ≠ 0 → n ^ k ≤ x.natAbs := by
    intro x hx hx0
    have := Int.natAbs_le_of_dvd_ne_zero hx hx0
    simpa [Int.natAbs_pow] using this
  have hC1le : C1 ≤ C1 + C1' + C2 + 1 := by omega
  have hC1'le : C1' ≤ C1 + C1' + C2 + 1 := by omega
  have hC2le : C2 ≤ C1 + C1' + C2 + 1 := by omega
  refine ⟨⟨_, hv1, hv1ne, hs1.trans (Nat.mul_le_mul_right _ hC1le)⟩, ?_, ⟨_, _, hv1, hv2, hdetv,
    hs1'.trans (Nat.mul_le_mul_right _ hC1'le), hs2.trans (Nat.mul_le_mul_right _ hC2le)⟩, ?_⟩
  · intro u hu hu0
    by_cases h1 : detZ u (vec B.p1 B.z1 n) = 0
    · have h2 : detZ u (vec B.p2 B.z2 n) ≠ 0 := by
        intro h2; apply hu0
        have hc := cramer u (vec B.p1 B.z1 n) (vec B.p2 B.z2 n)
        rw [h1, h2, zero_smul, zero_smul, sub_zero] at hc
        exact (smul_eq_zero.mp hc).resolve_left hdetv
      have hb := big _ (dvd_detZ hg hu hv2) h2
      have := abs_detZ_le u (vec B.p2 B.z2 n)
      have hmul : n ^ d1 * n ^ d2 ≤ 2 * supn u * (C2 * n ^ d2) := by
        rw [← hnk]; exact hb.trans (this.trans (Nat.mul_le_mul_left _ hs2))
      have : n ^ d1 ≤ 2 * C2 * supn u := by
        have h' : n ^ d1 * n ^ d2 ≤ (2 * C2 * supn u) * n ^ d2 := by
          calc n ^ d1 * n ^ d2 ≤ 2 * supn u * (C2 * n ^ d2) := hmul
            _ = (2 * C2 * supn u) * n ^ d2 := by ring
        exact Nat.le_of_mul_le_mul_right h' hpos2
      exact this.trans (Nat.mul_le_mul_right _ (by omega))
    · have hb := big _ (dvd_detZ hg hu hv1) h1
      have := abs_detZ_le u (vec B.p1 B.z1 n)
      have hmul : n ^ d1 * n ^ d2 ≤ 2 * supn u * (C1' * n ^ d2) := by
        rw [← hnk]; exact hb.trans (this.trans (Nat.mul_le_mul_left _ hs1'))
      have : n ^ d1 ≤ 2 * C1' * supn u := by
        have h' : n ^ d1 * n ^ d2 ≤ (2 * C1' * supn u) * n ^ d2 := by
          calc n ^ d1 * n ^ d2 ≤ 2 * supn u * (C1' * n ^ d2) := hmul
            _ = (2 * C1' * supn u) * n ^ d2 := by ring
        exact Nat.le_of_mul_le_mul_right h' hpos2
      exact this.trans (Nat.mul_le_mul_right _ (by omega))
  · intro u v hu hv huv
    have hw : ∃ w, (w = u ∨ w = v) ∧ detZ w (vec B.p1 B.z1 n) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h1 := hcon u (Or.inl rfl)
      have h2 := hcon v (Or.inr rfl)
      apply huv
      set w0 := vec B.p1 B.z1 n
      have e1 : w0.1 * detZ u v = u.1 * detZ w0 v - v.1 * detZ w0 u := by simp only [detZ]; ring
      have e2 : w0.2 * detZ u v = u.2 * detZ w0 v - v.2 * detZ w0 u := by simp only [detZ]; ring
      have f1 : detZ w0 u = 0 := by have : detZ w0 u = -detZ u w0 := by simp only [detZ]; ring
                                    rw [this, h1, neg_zero]
      have f2 : detZ w0 v = 0 := by have : detZ w0 v = -detZ v w0 := by simp only [detZ]; ring
                                    rw [this, h2, neg_zero]
      rw [f1, f2] at e1 e2
      simp only [mul_zero, sub_zero] at e1 e2
      by_contra hne
      apply hv1ne
      exact Prod.ext ((mul_eq_zero.mp e1).resolve_right hne) ((mul_eq_zero.mp e2).resolve_right hne)
    obtain ⟨w, hwuv, hdw⟩ := hw
    have hwL : InL p q k n w := by rcases hwuv with rfl | rfl <;> assumption
    have hb := big _ (dvd_detZ hg hwL hv1) hdw
    have := abs_detZ_le w (vec B.p1 B.z1 n)
    have hmul : n ^ d1 * n ^ d2 ≤ 2 * supn w * (C1 * n ^ d1) := by
      rw [← hnk]; exact hb.trans (this.trans (Nat.mul_le_mul_left _ hs1))
    have hle : n ^ d2 ≤ 2 * C1 * supn w := by
      have h' : n ^ d2 * n ^ d1 ≤ (2 * C1 * supn w) * n ^ d1 := by
        calc n ^ d2 * n ^ d1 = n ^ d1 * n ^ d2 := by ring
          _ ≤ 2 * supn w * (C1 * n ^ d1) := hmul
          _ = (2 * C1 * supn w) * n ^ d1 := by ring
      exact Nat.le_of_mul_le_mul_right h' hpos1
    have hwmax : supn w ≤ max (supn u) (supn v) := by
      rcases hwuv with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    calc n ^ d2 ≤ 2 * C1 * supn w := hle
      _ ≤ 2 * C1 * max (supn u) (supn v) := Nat.mul_le_mul_left _ hwmax
      _ ≤ 2 * (C1 + C1' + C2 + 1) * max (supn u) (supn v) := Nat.mul_le_mul_right _ (by omega)

end

end GenK
