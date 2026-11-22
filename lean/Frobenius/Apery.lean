import Frobenius.Certificate

/-!
# Apéry set, genus and pseudo-Frobenius numbers from a certificate

Continuation of `Frobenius.Certificate`: under the hypotheses of the certificate criterion
we prove
* the Apéry-set characterization: if `(i,j) ∈ R` and `x ≡ i b + j c (mod a)` then
  `x ∈ ⟨a,b,c⟩ ↔ i b + j c ≤ x`;
* the genus formula (2.3) of Lemma 2.1, in a subtraction-free form (`genus_uv`);
* the pseudo-Frobenius numbers: they are `ω(p) - a` for the maximal points `p` of `R`
  (`isPF_iff`), hence `PF = {F₁, F₂}` and type two when `w, y ≥ 1` (`pf_uv`, `type_uv`),
  and `PF = {F}` when `w = 0` or `y = 0` (`pf_rect_uv`).
-/

namespace FrobCert

variable {a b c l h w y q₁ q₂ : ℕ}

/-- Reduction with the extra information that at least one step is made when `(i,j) ∉ R`. -/
theorem reduce' (C : Cert a b c l h w y q₁ q₂) :
    ∀ s i j : ℕ, i * b + j * c = s →
      ∃ i' j' t : ℕ, InR l h w y i' j' ∧ i * b + j * c = i' * b + j' * c + t * a ∧
        (¬ InR l h w y i j → 1 ≤ t) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro i j hs
    by_cases hi : l ≤ i
    · obtain ⟨i', j', t, hR, he, -⟩ :=
        ih ((i - l) * b + (j + y) * c) (by
          have hq : 0 < a * q₁ := Nat.mul_pos C.ha C.q₁pos
          have : i * b = (i - l) * b + l * b := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hi]
          rw [← hs, this, ← C.rel₁]; nlinarith) (i - l) (j + y) rfl
      refine ⟨i', j', t + q₁, hR, ?_, fun _ => by have := C.q₁pos; omega⟩
      have : i * b = (i - l) * b + l * b := by rw [← Nat.add_mul, Nat.sub_add_cancel hi]
      rw [this, ← C.rel₁]
      nlinarith [he]
    · by_cases hj : h ≤ j
      · obtain ⟨i', j', t, hR, he, -⟩ :=
          ih ((i + w) * b + (j - h) * c) (by
            have hq : 0 < a * q₂ := Nat.mul_pos C.ha C.q₂pos
            have : j * c = (j - h) * c + h * c := by
              rw [← Nat.add_mul, Nat.sub_add_cancel hj]
            rw [← hs, this, ← C.rel₂]; nlinarith) (i + w) (j - h) rfl
        refine ⟨i', j', t + q₂, hR, ?_, fun _ => by have := C.q₂pos; omega⟩
        have : j * c = (j - h) * c + h * c := by rw [← Nat.add_mul, Nat.sub_add_cancel hj]
        rw [this, ← C.rel₂]
        nlinarith [he]
      · by_cases hk : l - w ≤ i ∧ h - y ≤ j
        · obtain ⟨hk1, hk2⟩ := hk
          have key : (l - w) * b + (h - y) * c = a * (q₁ + q₂) := by
            have e1 : (l - w) * b + w * b = l * b := by
              rw [← Nat.add_mul, Nat.sub_add_cancel C.hw.le]
            have e2 : (h - y) * c + y * c = h * c := by
              rw [← Nat.add_mul, Nat.sub_add_cancel C.hy.le]
            have r1 := C.rel₁
            have r2 := C.rel₂
            nlinarith
          have hdecomp : i * b + j * c
              = (i - (l - w)) * b + (j - (h - y)) * c + ((l - w) * b + (h - y) * c) := by
            have ei : i * b = (i - (l - w)) * b + (l - w) * b := by
              rw [← Nat.add_mul, Nat.sub_add_cancel hk1]
            have ej : j * c = (j - (h - y)) * c + (h - y) * c := by
              rw [← Nat.add_mul, Nat.sub_add_cancel hk2]
            rw [ei, ej]; ring
          obtain ⟨i', j', t, hR, he, -⟩ :=
            ih ((i - (l - w)) * b + (j - (h - y)) * c) (by
              have hq : 0 < a * (q₁ + q₂) := Nat.mul_pos C.ha (by have := C.q₁pos; omega)
              rw [← hs, hdecomp, key]; omega) (i - (l - w)) (j - (h - y)) rfl
          refine ⟨i', j', t + (q₁ + q₂), hR, ?_, fun _ => by have := C.q₁pos; omega⟩
          rw [hdecomp, key, he]; ring
        · have hin : InR l h w y i j := ⟨by omega, by omega, hk⟩
          exact ⟨i, j, 0, hin, by ring, fun hn => absurd hin hn⟩

/-- `R` is a down-set. -/
theorem inR_mono {i j i' j' : ℕ} (hR : InR l h w y i j) (hi : i' ≤ i) (hj : j' ≤ j) :
    InR l h w y i' j' := by
  obtain ⟨h1, h2, h3⟩ := hR
  exact ⟨by omega, by omega, fun ⟨h4, h5⟩ => h3 ⟨by omega, by omega⟩⟩

theorem exists_mul_modEq (ha : 0 < a) (cop : Nat.Coprime a b) (k : ℕ) :
    ∃ i₀ : ℕ, ((i₀ * b : ℕ) : ℤ) ≡ (k : ℤ) [ZMOD (a : ℤ)] := by
  obtain ⟨v, u, hv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr cop
  refine ⟨Int.toNat ((k : ℤ) * u % a), ?_⟩
  have hpos : (0 : ℤ) < a := by exact_mod_cast ha
  have hnn : 0 ≤ (k : ℤ) * u % a := Int.emod_nonneg _ hpos.ne'
  push_cast
  rw [Int.toNat_of_nonneg hnn]
  calc ((k : ℤ) * u % a) * b ≡ ((k : ℤ) * u) * b [ZMOD (a : ℤ)] :=
        Int.ModEq.mul_right _ (Int.mod_modEq _ _)
    _ = k * (u * b) := by ring
    _ = k * (1 - v * a) := by rw [← hv]; ring
    _ = k - (k * v) * a := by ring
    _ ≡ k [ZMOD (a : ℤ)] := by
        rw [Int.modEq_iff_dvd]; exact ⟨k * v, by ring⟩

/-- Every residue class modulo `a` is represented by a point of `R`. -/
theorem exists_inR (C : Cert a b c l h w y q₁ q₂) (k : ℕ) :
    ∃ i j, InR l h w y i j ∧ ((i * b + j * c : ℕ) : ℤ) ≡ (k : ℤ) [ZMOD (a : ℤ)] := by
  obtain ⟨i₀, hi₀⟩ := exists_mul_modEq C.ha C.cop k
  obtain ⟨i', j', t, hR', he⟩ := reduce C _ i₀ 0 rfl
  refine ⟨i', j', hR', ?_⟩
  have e : i₀ * b = (i' * b + j' * c) + t * a := by rw [← he]; ring
  have : ((i₀ * b : ℕ) : ℤ) ≡ ((i' * b + j' * c : ℕ) : ℤ) [ZMOD (a : ℤ)] := by
    rw [e, Int.modEq_iff_dvd]; exact ⟨-t, by push_cast; ring⟩
  exact this.symm.trans hi₀

/-- **Apéry characterization.** -/
theorem rep_iff_ge (C : Cert a b c l h w y q₁ q₂) {i j : ℕ} (hR : InR l h w y i j) (x : ℕ)
    (hx : (x : ℤ) ≡ ((i * b + j * c : ℕ) : ℤ) [ZMOD (a : ℤ)]) :
    Rep a b c x ↔ i * b + j * c ≤ x := by
  constructor
  · rintro ⟨α, i₀, j₀, rfl⟩
    obtain ⟨i', j', t, hR', he⟩ := reduce C _ i₀ j₀ rfl
    have e : α * a + i₀ * b + j₀ * c = (i' * b + j' * c) + (α + t) * a := by
      rw [add_assoc, he]; ring
    have h1 : ((i' * b + j' * c : ℕ) : ℤ) ≡ ((α * a + i₀ * b + j₀ * c : ℕ) : ℤ)
        [ZMOD (a : ℤ)] := by
      rw [e, Int.modEq_iff_dvd]; exact ⟨α + t, by push_cast; ring⟩
    obtain ⟨rfl, rfl⟩ := inj C hR' hR (h1.trans hx)
    rw [e]; exact Nat.le_add_right _ _
  · intro hle
    obtain ⟨s, hs⟩ := hx.symm.dvd
    have ha : (0 : ℤ) < a := by exact_mod_cast C.ha
    have hle' : ((i * b + j * c : ℕ) : ℤ) ≤ x := by exact_mod_cast hle
    have hs0 : 0 ≤ s := by
      by_contra hneg; push Not at hneg
      have : (a : ℤ) * s < 0 := by nlinarith
      linarith
    refine ⟨s.toNat, i, j, ?_⟩
    have : (x : ℤ) = s.toNat * a + i * b + j * c := by
      rw [Int.toNat_of_nonneg hs0]; push_cast at hs; linear_combination hs
    exact_mod_cast this

/-! ### Genus -/

/-- The genus of the numerical semigroup generated by `s`: the number of gaps. -/
noncomputable def genus (s : Set ℕ) : ℕ := Set.ncard {x : ℕ | x ∉ AddSubmonoid.closure s}

/-- `R` as a finset. -/
def RF (l h w y : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range l ×ˢ Finset.range h).filter (fun p => ¬ (l - w ≤ p.1 ∧ h - y ≤ p.2))

theorem mem_RF {p : ℕ × ℕ} : p ∈ RF l h w y ↔ InR l h w y p.1 p.2 := by
  simp [RF, InR, and_assoc]

/-- the weight `ω(p) = p₁ b + p₂ c` -/
def wt (b c : ℕ) (p : ℕ × ℕ) : ℕ := p.1 * b + p.2 * c

/-- gaps in the residue class of `ω(p)` -/
def gapF (a b c : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (wt b c p)).filter (fun x => x % a = wt b c p % a)

theorem card_filter_mod (N : ℕ) (ha : 0 < a) :
    ((Finset.range N).filter (fun x => x % a = N % a)).card = N / a := by
  have : (Finset.range N).filter (fun x => x % a = N % a) =
      (Finset.range (N / a)).image (fun k => N % a + k * a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, hmod⟩
      refine ⟨x / a, ?_, ?_⟩
      · have h1 := Nat.div_add_mod x a
        have h2 := Nat.div_add_mod N a
        by_contra hge; push Not at hge
        have : N / a * a ≤ x / a * a := Nat.mul_le_mul_right _ hge
        nlinarith
      · have := Nat.div_add_mod x a; rw [← hmod]; linarith
    · rintro ⟨k, hk, rfl⟩
      constructor
      · have h2 := Nat.div_add_mod N a
        have : (k + 1) * a ≤ N / a * a := Nat.mul_le_mul_right _ hk
        nlinarith
      · rw [Nat.add_mul_mod_self_right, Nat.mod_mod]
  rw [this, Finset.card_image_of_injective _ (fun k k' hk => by
    exact Nat.eq_of_mul_eq_mul_right ha (by omega)), Finset.card_range]

theorem genus_eq_sum (C : Cert a b c l h w y q₁ q₂) :
    genus {a, b, c} = ∑ p ∈ RF l h w y, wt b c p / a := by
  have hset : {x : ℕ | x ∉ AddSubmonoid.closure ({a, b, c} : Set ℕ)} =
      ↑((RF l h w y).biUnion (gapF a b c)) := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_closure_iff, Finset.coe_biUnion, Finset.mem_coe,
      Set.mem_iUnion, exists_prop, gapF, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hx
      obtain ⟨i, j, hR, hmod⟩ := exists_inR C x
      refine ⟨(i, j), mem_RF.mpr hR, ?_, ?_⟩
      · have := (rep_iff_ge C hR x hmod.symm).not.mp hx
        simp only [wt]; omega
      · simp only [wt]
        exact (Int.natCast_modEq_iff.mp hmod).symm
    · rintro ⟨p, hp, hlt, hmod⟩
      have hR := mem_RF.mp hp
      rw [rep_iff_ge C hR x (Int.natCast_modEq_iff.mpr hmod)]
      simp only [wt] at hlt; omega
  rw [genus, hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun p _ => card_filter_mod _ C.ha)
  · intro p hp p' hp' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [gapF, Finset.mem_filter] at hx hx'
    apply hne
    have hm : ((p.1 * b + p.2 * c : ℕ) : ℤ) ≡ ((p'.1 * b + p'.2 * c : ℕ) : ℤ) [ZMOD (a : ℤ)] :=
      Int.natCast_modEq_iff.mpr (by simp only [wt] at hx hx'; exact hx.2.symm.trans hx'.2)
    obtain ⟨h1, h2⟩ := inj C (mem_RF.mp hp) (mem_RF.mp hp') hm
    exact Prod.ext h1 h2

theorem sum_mod_eq (C : Cert a b c l h w y q₁ q₂) :
    ∑ p ∈ RF l h w y, wt b c p % a = ∑ t ∈ Finset.range a, t := by
  apply Finset.sum_bij (fun p _ => wt b c p % a)
  · intro p _; exact Finset.mem_range.mpr (Nat.mod_lt _ C.ha)
  · intro p hp p' hp' he
    have hm : ((p.1 * b + p.2 * c : ℕ) : ℤ) ≡ ((p'.1 * b + p'.2 * c : ℕ) : ℤ) [ZMOD (a : ℤ)] :=
      Int.natCast_modEq_iff.mpr he
    obtain ⟨h1, h2⟩ := inj C (mem_RF.mp hp) (mem_RF.mp hp') hm
    exact Prod.ext h1 h2
  · intro t ht
    obtain ⟨i, j, hR, hmod⟩ := exists_inR C t
    refine ⟨(i, j), mem_RF.mpr hR, ?_⟩
    have := Int.natCast_modEq_iff.mp hmod
    simp only [wt]; rw [this, Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
  · intro p _; rfl

theorem sum_product_wt (A B : Finset ℕ) :
    ∑ p ∈ A ×ˢ B, wt b c p = B.card * b * ∑ i ∈ A, i + A.card * c * ∑ j ∈ B, j := by
  rw [Finset.sum_product]
  simp only [wt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

theorem sum_range_two (n : ℕ) : (∑ i ∈ Finset.range (n + 1), i) * 2 = (n + 1) * n := by
  rw [Finset.sum_range_id_mul_two]; simp

theorem sum_Ico_two (m k : ℕ) : (∑ i ∈ Finset.Ico m (m + k), i) * 2 = k * (2 * m + k) - k := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, smul_eq_mul, add_mul, Finset.sum_range_id_mul_two]
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    have : (k + 1) * (2 * m + (k + 1)) - (k + 1) = (k + 1) * m * 2 + (k + 1) * k := by
      have h : (k + 1) ≤ (k + 1) * (2 * m + (k + 1)) := by nlinarith
      zify [h]; ring
    rw [this]

/-- The sum of the weights over `R` (in the parametrisation `l = w+u+1`, `h = y+v+1`). -/
theorem sum_wt_uv {u v : ℕ} :
    (∑ p ∈ RF (w + u + 1) (y + v + 1) w y, wt b c p) * 2
        + w * y * ((w + 2 * u + 1) * b + (y + 2 * v + 1) * c)
      = (w + u + 1) * (y + v + 1) * ((w + u) * b + (y + v) * c) := by
  set rect := Finset.range (w + u + 1) ×ˢ Finset.range (y + v + 1)
  have hsplit := Finset.sum_filter_add_sum_filter_not rect
    (fun p => w + u + 1 - w ≤ p.1 ∧ y + v + 1 - y ≤ p.2) (wt b c)
  have hblock : rect.filter (fun p => w + u + 1 - w ≤ p.1 ∧ y + v + 1 - y ≤ p.2) =
      Finset.Ico (u + 1) (u + 1 + w) ×ˢ Finset.Ico (v + 1) (v + 1 + y) := by
    ext p
    simp only [rect, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Ico]
    omega
  have hRF : rect.filter (fun p => ¬ (w + u + 1 - w ≤ p.1 ∧ y + v + 1 - y ≤ p.2)) =
      RF (w + u + 1) (y + v + 1) w y := rfl
  rw [hblock, hRF] at hsplit
  have hrect := sum_product_wt (b := b) (c := c) (Finset.range (w + u + 1)) (Finset.range (y + v + 1))
  have hblk := sum_product_wt (b := b) (c := c) (Finset.Ico (u + 1) (u + 1 + w))
    (Finset.Ico (v + 1) (v + 1 + y))
  simp only [Finset.card_range, Nat.card_Ico, Nat.add_sub_cancel_left] at hrect hblk
  have s1 := sum_range_two (w + u)
  have s2 := sum_range_two (y + v)
  have s3 := sum_Ico_two (u + 1) w
  have s4 := sum_Ico_two (v + 1) y
  have e3 : w * (2 * (u + 1) + w) - w = w * (w + 2 * u + 1) := by
    have : w ≤ w * (2 * (u + 1) + w) := by nlinarith
    zify [this]; ring
  have e4 : y * (2 * (v + 1) + y) - y = y * (y + 2 * v + 1) := by
    have : y ≤ y * (2 * (v + 1) + y) := by nlinarith
    zify [this]; ring
  rw [e3] at s3; rw [e4] at s4
  zify at hsplit hrect hblk s1 s2 s3 s4 ⊢
  linear_combination 2 * hsplit + 2 * hrect - 2 * hblk + (((y : ℤ) + v + 1) * b) * s1
    + (((w : ℤ) + u + 1) * c) * s2 - ((y : ℤ) * b) * s3 - ((w : ℤ) * c) * s4

/-- **Genus formula** (formula (2.3) of Lemma 2.1, without subtractions):
`2 a g + a² + w y ((w+2u+1) b + (y+2v+1) c) = (w+u+1)(y+v+1)((w+u) b + (y+v) c) + a`. -/
theorem genus_uv {u v : ℕ} (C : Cert a b c (w + u + 1) (y + v + 1) w y q₁ q₂) :
    genus {a, b, c} * a * 2 + a * a + w * y * ((w + 2 * u + 1) * b + (y + 2 * v + 1) * c)
      = (w + u + 1) * (y + v + 1) * ((w + u) * b + (y + v) * c) + a := by
  have hg := genus_eq_sum C
  have hmod := sum_mod_eq C
  have hdiv : ∑ p ∈ RF (w + u + 1) (y + v + 1) w y, wt b c p =
      (∑ p ∈ RF (w + u + 1) (y + v + 1) w y, wt b c p / a) * a +
        ∑ p ∈ RF (w + u + 1) (y + v + 1) w y, wt b c p % a := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => (Nat.div_add_mod' _ _).symm)
  have hw := sum_wt_uv (w := w) (y := y) (u := u) (v := v) (b := b) (c := c)
  have htri := Finset.sum_range_id_mul_two a
  have ha := C.ha
  have haa : a * (a - 1) + a = a * a := by
    rcases a with _ | a
    · omega
    · simp only [Nat.add_sub_cancel]; ring
  rw [← hg] at hdiv
  rw [hmod] at hdiv
  nlinarith [hdiv, hw, htri, haa]

/-! ### Pseudo-Frobenius numbers -/

/-- `x` is a pseudo-Frobenius number of the numerical semigroup generated by `s`. -/
def IsPF (s : Set ℕ) (x : ℕ) : Prop :=
  x ∉ AddSubmonoid.closure s ∧ ∀ z ∈ AddSubmonoid.closure s, z ≠ 0 → x + z ∈ AddSubmonoid.closure s

/-- `(i, j)` is a maximal point of `R`. -/
def IsMax (l h w y i j : ℕ) : Prop :=
  InR l h w y i j ∧ ¬ InR l h w y (i + 1) j ∧ ¬ InR l h w y i (j + 1)

theorem modEq_of_add {x a ω : ℕ} (h : x + a = ω) : (x : ℤ) ≡ (ω : ℤ) [ZMOD (a : ℤ)] := by
  rw [Int.modEq_iff_dvd]; exact ⟨1, by rw [← h]; push_cast; ring⟩

/-- **Pseudo-Frobenius numbers** are `ω(p) - a` for the maximal points `p` of `R`. -/
theorem isPF_iff (C : Cert a b c l h w y q₁ q₂) (hb : 0 < b) (hc : 0 < c) (x : ℕ) :
    IsPF {a, b, c} x ↔ ∃ i j, IsMax l h w y i j ∧ x + a = i * b + j * c := by
  have ha := C.ha
  simp only [IsPF, mem_closure_iff]
  constructor
  · rintro ⟨hx, hall⟩
    obtain ⟨i, j, hR, hmod⟩ := exists_inR C x
    have hlt : x < i * b + j * c := by
      have := (rep_iff_ge C hR x hmod.symm).not.mp hx; omega
    have hxa : Rep a b c (x + a) := hall a ⟨1, 0, 0, by ring⟩ (by omega)
    have hmod' : ((x + a : ℕ) : ℤ) ≡ ((i * b + j * c : ℕ) : ℤ) [ZMOD (a : ℤ)] := by
      have : ((x + a : ℕ) : ℤ) ≡ (x : ℤ) [ZMOD (a : ℤ)] := by
        rw [Int.modEq_iff_dvd]; exact ⟨-1, by push_cast; ring⟩
      exact this.trans hmod.symm
    have hge := (rep_iff_ge C hR (x + a) hmod').mp hxa
    have heq : x + a = i * b + j * c := by
      obtain ⟨s, hs⟩ := hmod.dvd
      have hlt' : (x : ℤ) < ((i * b + j * c : ℕ) : ℤ) := by exact_mod_cast hlt
      have hge' : ((i * b + j * c : ℕ) : ℤ) ≤ (x : ℤ) + a := by exact_mod_cast hge
      have ha' : (0 : ℤ) < a := by exact_mod_cast ha
      have hs1 : s = -1 := by
        have h1 : s < 0 := by nlinarith
        have h2 : -1 ≤ s := by nlinarith
        omega
      subst hs1
      have : ((i * b + j * c : ℕ) : ℤ) = x + a := by linarith
      exact_mod_cast this.symm
    refine ⟨i, j, ⟨hR, ?_, ?_⟩, heq⟩
    · intro hR1
      have hxb := hall b ⟨0, 1, 0, by ring⟩ (by omega)
      have hm : ((x + b : ℕ) : ℤ) ≡ (((i + 1) * b + j * c : ℕ) : ℤ) [ZMOD (a : ℤ)] :=
        modEq_of_add (by rw [← add_right_comm, heq]; ring)
      have := (rep_iff_ge C hR1 (x + b) hm).mp hxb
      have : (i + 1) * b + j * c = x + b + a := by rw [add_right_comm, heq]; ring
      omega
    · intro hR1
      have hxc := hall c ⟨0, 0, 1, by ring⟩ (by omega)
      have hm : ((x + c : ℕ) : ℤ) ≡ ((i * b + (j + 1) * c : ℕ) : ℤ) [ZMOD (a : ℤ)] :=
        modEq_of_add (by rw [← add_right_comm, heq]; ring)
      have := (rep_iff_ge C hR1 (x + c) hm).mp hxc
      have : i * b + (j + 1) * c = x + c + a := by rw [add_right_comm, heq]; ring
      omega
  · rintro ⟨i, j, ⟨hR, hm1, hm2⟩, heq⟩
    constructor
    · intro hx
      have := (rep_iff_ge C hR x (modEq_of_add heq)).mp hx
      omega
    · rintro z ⟨α, i₀, j₀, rfl⟩ hz
      rcases Nat.eq_zero_or_pos α with hα | hα
      · subst hα
        have hq : ¬ InR l h w y (i + i₀) (j + j₀) := by
          intro hq
          rcases Nat.eq_zero_or_pos i₀ with hi0 | hi0
          · have hj0 : 0 < j₀ := by
              rcases Nat.eq_zero_or_pos j₀ with hj0 | hj0
              · subst hi0; subst hj0; simp at hz
              · exact hj0
            exact hm2 (inR_mono hq (by omega) (by omega))
          · exact hm1 (inR_mono hq (by omega) (by omega))
        obtain ⟨i', j', t, hR', he, ht⟩ := reduce' C _ (i + i₀) (j + j₀) rfl
        have ht1 := ht hq
        refine ⟨t - 1, i', j', ?_⟩
        have e1 : x + (0 * a + i₀ * b + j₀ * c) + a = (i + i₀) * b + (j + j₀) * c := by
          rw [show x + (0 * a + i₀ * b + j₀ * c) + a = (x + a) + (i₀ * b + j₀ * c) by ring, heq]
          ring
        rw [he] at e1
        have : t * a = (t - 1) * a + a := by
          rcases t with _ | t
          · omega
          · simp only [Nat.add_sub_cancel]; ring
        omega
      · refine ⟨α - 1, i + i₀, j + j₀, ?_⟩
        have : α * a = (α - 1) * a + a := by
          rcases α with _ | α
          · omega
          · simp only [Nat.add_sub_cancel]; ring
        rw [this]
        have e : x + a = i * b + j * c := heq
        nlinarith [e]

theorem isMax_iff (hwl : w < l) (hyh : y < h) (hw1 : 1 ≤ w) (hy1 : 1 ≤ y) {i j : ℕ} :
    IsMax l h w y i j ↔ (i = l - 1 ∧ j = h - y - 1) ∨ (i = l - w - 1 ∧ j = h - 1) := by
  simp only [IsMax, InR]
  omega

theorem isMax_iff_rect (hwl : w < l) (hyh : y < h) (hdeg : w = 0 ∨ y = 0) {i j : ℕ} :
    IsMax l h w y i j ↔ i = l - 1 ∧ j = h - 1 := by
  simp only [IsMax, InR]
  omega

/-- Pseudo-Frobenius numbers when `w, y ≥ 1`: exactly `F₁` and `F₂`. -/
theorem pf_uv {u v P₁ P₂ : ℕ} (C : Cert a b c (w + u + 1) (y + v + 1) w y q₁ q₂)
    (hb : 0 < b) (hc : 0 < c) (hw1 : 1 ≤ w) (hy1 : 1 ≤ y)
    (h₁ : P₁ + a = (w + u) * b + v * c) (h₂ : P₂ + a = u * b + (y + v) * c) (x : ℕ) :
    IsPF {a, b, c} x ↔ x = P₁ ∨ x = P₂ := by
  rw [isPF_iff C hb hc]
  constructor
  · rintro ⟨i, j, hM, hx⟩
    rcases (isMax_iff C.hw C.hy hw1 hy1).mp hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      have e1 : w + u + 1 - 1 = w + u := by omega
      have e2 : y + v + 1 - y - 1 = v := by omega
      rw [e1, e2] at hx
      omega
    · right
      have e1 : w + u + 1 - w - 1 = u := by omega
      have e2 : y + v + 1 - 1 = y + v := by omega
      rw [e1, e2] at hx
      omega
  · rintro (rfl | rfl)
    · exact ⟨w + u, v, (isMax_iff C.hw C.hy hw1 hy1).mpr (Or.inl ⟨by omega, by omega⟩), h₁⟩
    · exact ⟨u, y + v, (isMax_iff C.hw C.hy hw1 hy1).mpr (Or.inr ⟨by omega, by omega⟩), h₂⟩

/-- The two pseudo-Frobenius numbers are distinct, so the type is two. -/
theorem type_uv {u v P₁ P₂ : ℕ} (C : Cert a b c (w + u + 1) (y + v + 1) w y q₁ q₂)
    (hb : 0 < b) (hc : 0 < c) (hw1 : 1 ≤ w) (hy1 : 1 ≤ y)
    (h₁ : P₁ + a = (w + u) * b + v * c) (h₂ : P₂ + a = u * b + (y + v) * c) :
    Set.ncard {x | IsPF {a, b, c} x} = 2 := by
  have hset : {x | IsPF {a, b, c} x} = {P₁, P₂} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact pf_uv C hb hc hw1 hy1 h₁ h₂ x
  have hne : P₁ ≠ P₂ := by
    intro hPP
    have hR1 : InR (w + u + 1) (y + v + 1) w y (w + u) v := ⟨by omega, by omega, by omega⟩
    have hR2 : InR (w + u + 1) (y + v + 1) w y u (y + v) := ⟨by omega, by omega, by omega⟩
    have hm : (((w + u) * b + v * c : ℕ) : ℤ) ≡ ((u * b + (y + v) * c : ℕ) : ℤ) [ZMOD (a : ℤ)] := by
      rw [← h₁, ← h₂, hPP]
    have := (inj C hR1 hR2 hm).1
    omega
  rw [hset, Set.ncard_pair hne]

/-- Pseudo-Frobenius numbers when `w = 0` or `y = 0` (rectangular `R`): only `F`. -/
theorem pf_rect_uv {u v P : ℕ} (C : Cert a b c (w + u + 1) (y + v + 1) w y q₁ q₂)
    (hb : 0 < b) (hc : 0 < c) (hdeg : w = 0 ∨ y = 0)
    (hP : P + a = (w + u) * b + (y + v) * c) (x : ℕ) :
    IsPF {a, b, c} x ↔ x = P := by
  rw [isPF_iff C hb hc]
  constructor
  · rintro ⟨i, j, hM, hx⟩
    obtain ⟨rfl, rfl⟩ := (isMax_iff_rect C.hw C.hy hdeg).mp hM
    have e1 : w + u + 1 - 1 = w + u := by omega
    have e2 : y + v + 1 - 1 = y + v := by omega
    rw [e1, e2] at hx
    omega
  · rintro rfl
    exact ⟨w + u, y + v, (isMax_iff_rect C.hw C.hy hdeg).mpr ⟨by omega, by omega⟩, hP⟩

end FrobCert
