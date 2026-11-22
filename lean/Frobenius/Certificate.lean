import Mathlib

/-!
# A certificate criterion for the Frobenius number of `⟨a, b, c⟩`

This file formalizes the Frobenius-number part of Lemma 2.1 of the paper
"The order of growth of the Frobenius number of three consecutive k-th powers".

Given natural numbers `l h w y q₁ q₂` with
* `w < l`, `y < h`,
* `l * h = a + w * y`,
* `y * c + a * q₁ = l * b` and `w * b + a * q₂ = h * c` with `0 < q₁`, `0 < q₂`,

and `gcd(a, b) = 1`, the Frobenius number of `⟨a, b, c⟩` is `M - a`, where
`M = max ((l-1) b + (h-y-1) c) ((l-w-1) b + (h-1) c)`.

The proof avoids counting arguments: every pair `(i, j)` can be moved into the L-shaped region
`R` by weight-decreasing moves that preserve the residue of `i b + j c` modulo `a`, and two
points of `R` with the same residue coincide (a short lattice argument).
-/

namespace FrobCert

/-- `x` is a nonnegative integer combination of `a`, `b`, `c`. -/
def Rep (a b c x : ℕ) : Prop := ∃ α i j : ℕ, x = α * a + i * b + j * c

theorem mem_closure_iff (a b c x : ℕ) :
    x ∈ AddSubmonoid.closure ({a, b, c} : Set ℕ) ↔ Rep a b c x := by
  constructor
  · intro hx
    let T : AddSubmonoid ℕ :=
      { carrier := {x | Rep a b c x}
        zero_mem' := ⟨0, 0, 0, by simp⟩
        add_mem' := by
          rintro x y ⟨α, i, j, rfl⟩ ⟨β, k, m, rfl⟩
          exact ⟨α + β, i + k, j + m, by ring⟩ }
    have hsub : ({a, b, c} : Set ℕ) ⊆ T := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by ring⟩
      · exact ⟨0, 1, 0, by ring⟩
      · exact ⟨0, 0, 1, by ring⟩
    exact (AddSubmonoid.closure_le.mpr hsub) hx
  · rintro ⟨α, i, j, rfl⟩
    have ha : a ∈ AddSubmonoid.closure ({a, b, c} : Set ℕ) :=
      AddSubmonoid.subset_closure (by simp)
    have hb : b ∈ AddSubmonoid.closure ({a, b, c} : Set ℕ) :=
      AddSubmonoid.subset_closure (by simp)
    have hc : c ∈ AddSubmonoid.closure ({a, b, c} : Set ℕ) :=
      AddSubmonoid.subset_closure (by simp)
    have h1 := AddSubmonoid.nsmul_mem _ ha α
    have h2 := AddSubmonoid.nsmul_mem _ hb i
    have h3 := AddSubmonoid.nsmul_mem _ hc j
    simp only [smul_eq_mul] at h1 h2 h3
    exact add_mem (add_mem h1 h2) h3

/-- The hypotheses of the certificate criterion. -/
structure Cert (a b c l h w y q₁ q₂ : ℕ) : Prop where
  ha : 0 < a
  cop : Nat.Coprime a b
  hw : w < l
  hy : y < h
  det : l * h = a + w * y
  rel₁ : y * c + a * q₁ = l * b
  rel₂ : w * b + a * q₂ = h * c
  q₁pos : 0 < q₁
  q₂pos : 0 < q₂

variable {a b c l h w y q₁ q₂ : ℕ}

/-- membership in the L-shaped region `R` -/
def InR (l h w y i j : ℕ) : Prop := i < l ∧ j < h ∧ ¬ (l - w ≤ i ∧ h - y ≤ j)

/-- Reduction: every `(i, j)` has a representative in `R` of the form
`i b + j c = i' b + j' c + t a`. -/
theorem reduce (C : Cert a b c l h w y q₁ q₂) :
    ∀ s i j : ℕ, i * b + j * c = s →
      ∃ i' j' t : ℕ, InR l h w y i' j' ∧ i * b + j * c = i' * b + j' * c + t * a := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro i j hs
    by_cases hi : l ≤ i
    · -- move (i, j) ↦ (i - l, j + y)
      obtain ⟨i', j', t, hR, he⟩ :=
        ih ((i - l) * b + (j + y) * c) (by
          have hq : 0 < a * q₁ := Nat.mul_pos C.ha C.q₁pos
          have : i * b = (i - l) * b + l * b := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hi]
          rw [← hs, this, ← C.rel₁]; nlinarith) (i - l) (j + y) rfl
      refine ⟨i', j', t + q₁, hR, ?_⟩
      have : i * b = (i - l) * b + l * b := by rw [← Nat.add_mul, Nat.sub_add_cancel hi]
      rw [this, ← C.rel₁]
      nlinarith [he]
    · by_cases hj : h ≤ j
      · -- move (i, j) ↦ (i + w, j - h)
        obtain ⟨i', j', t, hR, he⟩ :=
          ih ((i + w) * b + (j - h) * c) (by
            have hq : 0 < a * q₂ := Nat.mul_pos C.ha C.q₂pos
            have : j * c = (j - h) * c + h * c := by
              rw [← Nat.add_mul, Nat.sub_add_cancel hj]
            rw [← hs, this, ← C.rel₂]; nlinarith) (i + w) (j - h) rfl
        refine ⟨i', j', t + q₂, hR, ?_⟩
        have : j * c = (j - h) * c + h * c := by rw [← Nat.add_mul, Nat.sub_add_cancel hj]
        rw [this, ← C.rel₂]
        nlinarith [he]
      · by_cases hk : l - w ≤ i ∧ h - y ≤ j
        · -- move (i, j) ↦ (i - (l - w), j - (h - y))
          obtain ⟨hk1, hk2⟩ := hk
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
          obtain ⟨i', j', t, hR, he⟩ :=
            ih ((i - (l - w)) * b + (j - (h - y)) * c) (by
              have hq : 0 < a * (q₁ + q₂) := Nat.mul_pos C.ha (by have := C.q₁pos; omega)
              rw [← hs, hdecomp, key]; omega) (i - (l - w)) (j - (h - y)) rfl
          refine ⟨i', j', t + (q₁ + q₂), hR, ?_⟩
          rw [hdecomp, key, he]; ring
        · exact ⟨i, j, 0, ⟨by omega, by omega, hk⟩, by ring⟩

/-- Two points of `R` with weights congruent modulo `a` coincide. -/
theorem inj (C : Cert a b c l h w y q₁ q₂) {i j i' j' : ℕ}
    (hR : InR l h w y i j) (hR' : InR l h w y i' j')
    (hmod : ((i * b + j * c : ℕ) : ℤ) ≡ ((i' * b + j' * c : ℕ) : ℤ) [ZMOD (a : ℤ)]) :
    i = i' ∧ j = j' := by
  obtain ⟨hi, hj, hc⟩ := hR
  obtain ⟨hi', hj', hc'⟩ := hR'
  set di : ℤ := (i : ℤ) - i' with hdi
  set dj : ℤ := (j : ℤ) - j' with hdj
  have hdiv : (a : ℤ) ∣ di * b + dj * c := by
    have := (Int.ModEq.dvd hmod.symm)
    have e : ((i * b + j * c : ℕ) : ℤ) - ((i' * b + j' * c : ℕ) : ℤ) = di * b + dj * c := by
      push_cast; ring
    rw [e] at this; exact this
  have r1 : (y : ℤ) * c + a * q₁ = l * b := by exact_mod_cast C.rel₁
  have r2 : (w : ℤ) * b + a * q₂ = h * c := by exact_mod_cast C.rel₂
  have dt : (l : ℤ) * h = a + w * y := by exact_mod_cast C.det
  have cop : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr C.cop
  -- a ∣ di h + dj w  and  a ∣ di y + dj l
  have d1 : (a : ℤ) ∣ di * h + dj * w := by
    have : (a : ℤ) ∣ (di * h + dj * w) * b := by
      have e : (di * h + dj * w) * b = h * (di * b + dj * c) - dj * (a * q₂) := by
        linear_combination (dj) * r2
      rw [e]; exact dvd_sub (dvd_mul_of_dvd_right hdiv _) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    exact cop.dvd_of_dvd_mul_right this
  have d2 : (a : ℤ) ∣ di * y + dj * l := by
    have : (a : ℤ) ∣ (di * y + dj * l) * b := by
      have e : (di * y + dj * l) * b = y * (di * b + dj * c) + dj * (a * q₁) := by
        linear_combination (-dj) * r1
      rw [e]; exact dvd_add (dvd_mul_of_dvd_right hdiv _) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    exact cop.dvd_of_dvd_mul_right this
  obtain ⟨α, hα⟩ := d1
  obtain ⟨β, hβ⟩ := d2
  have ha : (0 : ℤ) < a := by exact_mod_cast C.ha
  -- di = α l - β w, dj = β h - α y
  have edi : di = α * l - β * w := by
    have : (a : ℤ) * di = a * (α * l - β * w) := by
      linear_combination (l : ℤ) * hα - (w : ℤ) * hβ - di * dt
    exact mul_left_cancel₀ ha.ne' this
  have edj : dj = β * h - α * y := by
    have : (a : ℤ) * dj = a * (β * h - α * y) := by
      linear_combination (-(y : ℤ)) * hα + (h : ℤ) * hβ - dj * dt
    exact mul_left_cancel₀ ha.ne' this
  -- bounds
  have hwl : (w : ℤ) < l := by exact_mod_cast C.hw
  have hyh : (y : ℤ) < h := by exact_mod_cast C.hy
  have hi0 : (0 : ℤ) ≤ i := by positivity
  have hi0' : (0 : ℤ) ≤ i' := by positivity
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hj0' : (0 : ℤ) ≤ j' := by positivity
  have hil : (i : ℤ) < l := by exact_mod_cast hi
  have hil' : (i' : ℤ) < l := by exact_mod_cast hi'
  have hjh : (j : ℤ) < h := by exact_mod_cast hj
  have hjh' : (j' : ℤ) < h := by exact_mod_cast hj'
  have hw0 : (0 : ℤ) ≤ w := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  -- corner conditions in ℤ
  have corner : ∀ p q : ℕ, ¬ (l - w ≤ p ∧ h - y ≤ q) →
      ((p : ℤ) < l - w ∨ (q : ℤ) < h - y) := by
    intro p q hpq
    by_contra hcon
    push Not at hcon
    apply hpq
    constructor
    · have := hcon.1; omega
    · have := hcon.2; omega
  have cij := corner i j hc
  have cij' := corner i' j' hc'
  -- now the case analysis on α, β
  have hLW : (0 : ℤ) ≤ (l : ℤ) - w := by linarith
  have hHY : (0 : ℤ) ≤ (h : ℤ) - y := by linarith
  have hl0 : (0 : ℤ) ≤ l := by positivity
  have hh0 : (0 : ℤ) ≤ h := by positivity
  have di_lo : -(l : ℤ) < di := by rw [hdi]; linarith
  have di_hi : di < (l : ℤ) := by rw [hdi]; linarith
  have dj_lo : -(h : ℤ) < dj := by rw [hdj]; linarith
  have dj_hi : dj < (h : ℤ) := by rw [hdj]; linarith
  have hαβ : α = 0 ∧ β = 0 := by
    rcases lt_trichotomy α 0 with hα0 | hα0 | hα0 <;>
    rcases lt_trichotomy β 0 with hβ0 | hβ0 | hβ0
    · -- α < 0, β < 0
      exfalso
      rcases lt_trichotomy α β with h' | h' | h'
      · have p1 : α * l ≤ (β - 1) * l := mul_le_mul_of_nonneg_right (by omega) hl0
        have p2 : β * ((l : ℤ) - w) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ0.le hLW
        have e1 : (β - 1) * (l : ℤ) = β * l - l := by ring
        have e2 : β * ((l : ℤ) - w) = β * l - β * w := by ring
        have : di ≤ -(l : ℤ) := by rw [edi]; linarith
        linarith
      · subst h'
        have p1 : α * ((l : ℤ) - w) ≤ (-1) * ((l : ℤ) - w) :=
          mul_le_mul_of_nonneg_right (by omega) hLW
        have p2 : α * ((h : ℤ) - y) ≤ (-1) * ((h : ℤ) - y) :=
          mul_le_mul_of_nonneg_right (by omega) hHY
        have e1 : di = α * ((l : ℤ) - w) := by rw [edi]; ring
        have e2 : dj = α * ((h : ℤ) - y) := by rw [edj]; ring
        clear edi edj
        rcases cij' with h3 | h3
        · have : (i' : ℤ) = i - di := by rw [hdi]; ring
          linarith
        · have : (j' : ℤ) = j - dj := by rw [hdj]; ring
          linarith
      · have p1 : β * h ≤ (α - 1) * h := mul_le_mul_of_nonneg_right (by omega) hh0
        have p2 : α * ((h : ℤ) - y) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hα0.le hHY
        have e1 : (α - 1) * (h : ℤ) = α * h - h := by ring
        have e2 : α * ((h : ℤ) - y) = α * h - α * y := by ring
        have : dj ≤ -(h : ℤ) := by rw [edj]; linarith
        linarith
    · exfalso; subst hβ0
      have p1 : α * l ≤ (-1) * l := mul_le_mul_of_nonneg_right (by omega) hl0
      have : di ≤ -(l : ℤ) := by rw [edi]; linarith
      linarith
    · exfalso
      have p1 : α * l ≤ (-1) * l := mul_le_mul_of_nonneg_right (by omega) hl0
      have p2 : 0 ≤ β * w := mul_nonneg hβ0.le hw0
      have : di ≤ -(l : ℤ) := by rw [edi]; linarith
      linarith
    · exfalso; subst hα0
      have p1 : β * h ≤ (-1) * h := mul_le_mul_of_nonneg_right (by omega) hh0
      have : dj ≤ -(h : ℤ) := by rw [edj]; linarith
      linarith
    · exact ⟨hα0, hβ0⟩
    · exfalso; subst hα0
      have p1 : 1 * (h : ℤ) ≤ β * h := mul_le_mul_of_nonneg_right (by omega) hh0
      have : (h : ℤ) ≤ dj := by rw [edj]; linarith
      linarith
    · exfalso
      have p1 : 1 * (l : ℤ) ≤ α * l := mul_le_mul_of_nonneg_right (by omega) hl0
      have p2 : β * w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ0.le hw0
      have : (l : ℤ) ≤ di := by rw [edi]; linarith
      linarith
    · exfalso; subst hβ0
      have p1 : 1 * (l : ℤ) ≤ α * l := mul_le_mul_of_nonneg_right (by omega) hl0
      have : (l : ℤ) ≤ di := by rw [edi]; linarith
      linarith
    · -- α > 0, β > 0
      exfalso
      rcases lt_trichotomy α β with h' | h' | h'
      · have p1 : (α + 1) * h ≤ β * h := mul_le_mul_of_nonneg_right (by omega) hh0
        have p2 : 0 ≤ α * ((h : ℤ) - y) := mul_nonneg hα0.le hHY
        have e1 : (α + 1) * (h : ℤ) = α * h + h := by ring
        have e2 : α * ((h : ℤ) - y) = α * h - α * y := by ring
        have : (h : ℤ) ≤ dj := by rw [edj]; linarith
        linarith
      · subst h'
        have p1 : 1 * ((l : ℤ) - w) ≤ α * ((l : ℤ) - w) :=
          mul_le_mul_of_nonneg_right (by omega) hLW
        have p2 : 1 * ((h : ℤ) - y) ≤ α * ((h : ℤ) - y) :=
          mul_le_mul_of_nonneg_right (by omega) hHY
        have e1 : di = α * ((l : ℤ) - w) := by rw [edi]; ring
        have e2 : dj = α * ((h : ℤ) - y) := by rw [edj]; ring
        clear edi edj
        rcases cij with h3 | h3
        · have : (i : ℤ) = i' + di := by rw [hdi]; ring
          linarith
        · have : (j : ℤ) = j' + dj := by rw [hdj]; ring
          linarith
      · have p1 : (β + 1) * l ≤ α * l := mul_le_mul_of_nonneg_right (by omega) hl0
        have p2 : 0 ≤ β * ((l : ℤ) - w) := mul_nonneg hβ0.le hLW
        have e1 : (β + 1) * (l : ℤ) = β * l + l := by ring
        have e2 : β * ((l : ℤ) - w) = β * l - β * w := by ring
        have : (l : ℤ) ≤ di := by rw [edi]; linarith
        linarith
  obtain ⟨rfl, rfl⟩ := hαβ
  constructor <;> omega

/-- Points of `R` have weight at most `M`. -/
theorem weight_le (_C : Cert a b c l h w y q₁ q₂) {i j : ℕ} (hR : InR l h w y i j) :
    i * b + j * c ≤ max ((l - 1) * b + (h - y - 1) * c) ((l - w - 1) * b + (h - 1) * c) := by
  obtain ⟨hi, hj, hc⟩ := hR
  by_cases hjy : j < h - y
  · apply le_max_of_le_left
    have : i ≤ l - 1 := by omega
    have : j ≤ h - y - 1 := by omega
    gcongr
  · apply le_max_of_le_right
    have : i ≤ l - w - 1 := by omega
    have : j ≤ h - 1 := by omega
    gcongr

/-- **Certificate criterion** (Frobenius part of Lemma 2.1). -/
theorem frobenius_of_cert (C : Cert a b c l h w y q₁ q₂)
    (haM : a ≤ max ((l - 1) * b + (h - y - 1) * c) ((l - w - 1) * b + (h - 1) * c)) :
    FrobeniusNumber (max ((l - 1) * b + (h - y - 1) * c) ((l - w - 1) * b + (h - 1) * c) - a)
      {a, b, c} := by
  set M := max ((l - 1) * b + (h - y - 1) * c) ((l - w - 1) * b + (h - 1) * c) with hM
  rw [frobeniusNumber_iff]
  have hwl := C.hw
  have hyh := C.hy
  have hl : 1 ≤ l := by omega
  have hh : 1 ≤ h := by omega
  constructor
  · -- M - a is not representable
    rw [mem_closure_iff]
    rintro ⟨α, i, j, hrep⟩
    -- the corner realising M
    obtain ⟨p, q, hpq, hMpq⟩ : ∃ p q : ℕ, InR l h w y p q ∧ M = p * b + q * c := by
      rcases le_total ((l - 1) * b + (h - y - 1) * c) ((l - w - 1) * b + (h - 1) * c) with hle | hle
      · refine ⟨l - w - 1, h - 1, ⟨by omega, by omega, by omega⟩, ?_⟩
        rw [hM, max_eq_right hle]
      · refine ⟨l - 1, h - y - 1, ⟨by omega, by omega, by omega⟩, ?_⟩
        rw [hM, max_eq_left hle]
    obtain ⟨i', j', t, hR', he⟩ := reduce C _ i j rfl
    have hsum : p * b + q * c = i' * b + j' * c + (t + α + 1) * a := by
      have : M = M - a + a := (Nat.sub_add_cancel haM).symm
      rw [← hMpq, this, hrep]
      have he' := he
      zify at he' ⊢
      linear_combination he'
    have hmod : ((p * b + q * c : ℕ) : ℤ) ≡ ((i' * b + j' * c : ℕ) : ℤ) [ZMOD (a : ℤ)] := by
      rw [hsum]
      apply Int.ModEq.symm
      rw [Int.modEq_iff_dvd]
      exact ⟨t + α + 1, by push_cast; ring⟩
    obtain ⟨rfl, rfl⟩ := inj C hpq hR' hmod
    have := C.ha
    nlinarith
  · -- every k > M - a is representable
    intro k hk
    rw [mem_closure_iff]
    -- choose i₀ with i₀ b ≡ k (mod a)
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ℕ, ((i₀ * b : ℕ) : ℤ) ≡ (k : ℤ) [ZMOD (a : ℤ)] := by
      obtain ⟨v, u, hv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr C.cop
      refine ⟨Int.toNat ((k : ℤ) * u % a), ?_⟩
      have hpos : (0 : ℤ) < a := by exact_mod_cast C.ha
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
    obtain ⟨i', j', t, hR', he⟩ := reduce C _ i₀ 0 rfl
    have hw := weight_le C hR'
    set W := i' * b + j' * c with hW
    have hmodW : (W : ℤ) ≡ (k : ℤ) [ZMOD (a : ℤ)] := by
      have : ((i₀ * b : ℕ) : ℤ) ≡ (W : ℤ) [ZMOD (a : ℤ)] := by
        have e : i₀ * b = W + t * a := by rw [← he]; ring
        rw [e, Int.modEq_iff_dvd]; exact ⟨-t, by push_cast; ring⟩
      exact this.symm.trans hi₀
    -- k ≥ W
    have hkW : W ≤ k := by
      by_contra hlt
      push Not at hlt
      obtain ⟨s, hs⟩ := (Int.ModEq.dvd hmodW)
      have ha : (0 : ℤ) < a := by exact_mod_cast C.ha
      have hk' : (k : ℤ) < W := by exact_mod_cast hlt
      have hs1 : s < 0 := by
        by_contra hs0; push Not at hs0; nlinarith
      have : (k : ℤ) ≤ W - a := by nlinarith
      have hMa : ((M - a : ℕ) : ℤ) = (M : ℤ) - a := by push_cast [Nat.cast_sub haM]; ring
      have : (k : ℤ) ≤ M - a := by
        have : (W : ℤ) ≤ M := by exact_mod_cast hw
        linarith
      have hk2 : ((M - a : ℕ) : ℤ) < k := by exact_mod_cast hk
      linarith
    obtain ⟨s, hs⟩ := (Int.ModEq.dvd hmodW)
    have ha : (0 : ℤ) < a := by exact_mod_cast C.ha
    have hs0 : 0 ≤ s := by
      by_contra hneg; push Not at hneg
      have : (k : ℤ) - W < 0 := by rw [hs]; nlinarith
      have : (W : ℤ) ≤ k := by exact_mod_cast hkW
      linarith
    refine ⟨s.toNat, i', j', ?_⟩
    have : (k : ℤ) = s.toNat * a + i' * b + j' * c := by
      have hW' : (W : ℤ) = i' * b + j' * c := by rw [hW]; push_cast; ring
      rw [Int.toNat_of_nonneg hs0]; linear_combination hs + hW'
    exact_mod_cast this

/-- The certificate criterion with the subtractions eliminated:
`l = w + u + 1`, `h = y + v + 1`, and the Frobenius number `F` given by `F + a = M`. -/
theorem frob_uv {a b c w y u v q₁ q₂ F : ℕ} (ha : 0 < a) (cop : Nat.Coprime a b)
    (det : (w + u + 1) * (y + v + 1) = a + w * y)
    (rel₁ : y * c + a * q₁ = (w + u + 1) * b) (rel₂ : w * b + a * q₂ = (y + v + 1) * c)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hF : F + a = max ((w + u) * b + v * c) (u * b + (y + v) * c)) :
    FrobeniusNumber F {a, b, c} := by
  have C : Cert a b c (w + u + 1) (y + v + 1) w y q₁ q₂ :=
    ⟨ha, cop, by omega, by omega, det, rel₁, rel₂, hq₁, hq₂⟩
  have e1 : w + u + 1 - 1 = w + u := by omega
  have e2 : y + v + 1 - y - 1 = v := by omega
  have e3 : w + u + 1 - w - 1 = u := by omega
  have e4 : y + v + 1 - 1 = y + v := by omega
  have key := frobenius_of_cert C (by rw [e1, e2, e3, e4, ← hF]; omega)
  rw [e1, e2, e3, e4, ← hF, Nat.add_sub_cancel] at key
  exact key

end FrobCert
