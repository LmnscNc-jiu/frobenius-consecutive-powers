import Frobenius.Apery

/-!
# Existence of an L-shaped certificate for three generators

For positive integers `a < c`, `b` with `gcd(a, b) = gcd(b, c) = 1` we construct parameters
`l h w y q₁ q₂` satisfying the hypotheses `Cert` of the certificate criterion (Lemma 2.1).
This is the classical fact that the Apéry set of `⟨a, b, c⟩` with respect to `a` is described
by an L-shaped region; we give a self-contained proof.

Construction: `l` is the least `x ≥ 1` such that `x b ≡ z c (mod a)` for some `z` with `z c < x b`,
and `y` is the least such `z`; symmetrically `h` and `w` with the roles of `b` and `c` exchanged.
The identity `l h - w y = a` is proved by showing that the L-shaped region contains no nonzero
point of the relation lattice, so that `(a, 0)` and `(i₀, 1)` (with `i₀ b + c ≡ 0`) are integer
combinations of `(l, -y)` and `(-w, h)`.
-/

namespace FrobCert

open Classical

section LShape

variable {a b c : ℕ}

/-- candidate for `(l, y)`: `x ≥ 1`, `z c < x b`, `a ∣ x b - z c` -/
def Lw (a b c x z : ℕ) : Prop :=
  1 ≤ x ∧ z * c < x * b ∧ (a : ℤ) ∣ (x : ℤ) * b - (z : ℤ) * c

/-- candidate for `(h, w)`: `x ≥ 1`, `z b < x c`, `a ∣ x c - z b` -/
def Hw (a b c x z : ℕ) : Prop :=
  1 ≤ x ∧ z * b < x * c ∧ (a : ℤ) ∣ (x : ℤ) * c - (z : ℤ) * b

theorem exL (ha : 0 < a) (hb : 0 < b) : ∃ x z, Lw a b c x z :=
  ⟨a, 0, ha, by simp; exact ⟨ha, hb⟩, ⟨b, by ring⟩⟩

theorem exH (ha : 0 < a) (hc : 0 < c) : ∃ x z, Hw a b c x z :=
  ⟨a, 0, ha, by simp; exact ⟨ha, hc⟩, ⟨c, by ring⟩⟩

/-- Every point `(x, 0)` with `1 ≤ x`, `a ∣ x b` is a candidate. -/
theorem lw_axis {x : ℕ} (hx : 1 ≤ x) (hb : 0 < b) (h : (a : ℤ) ∣ (x : ℤ) * b) : Lw a b c x 0 :=
  ⟨hx, by simp; exact ⟨by omega, hb⟩, by simpa using h⟩

theorem hw_axis {x : ℕ} (hx : 1 ≤ x) (hc : 0 < c) (h : (a : ℤ) ∣ (x : ℤ) * c) : Hw a b c x 0 :=
  ⟨hx, by simp; exact ⟨by omega, hc⟩, by simpa using h⟩

/-- Main construction. -/
theorem exists_cert (ha : 0 < a) (hb : 0 < b) (hac : a < c) (cop : Nat.Coprime a b)
    (copbc : Nat.Coprime b c) :
    ∃ l h w y q₁ q₂ : ℕ, Cert a b c l h w y q₁ q₂ := by
  have hc : 0 < c := by omega
  have HL : ∃ x z, Lw a b c x z := exL ha hb
  have HH : ∃ x z, Hw a b c x z := exH ha hc
  -- the parameters and their minimality
  set l := Nat.find HL with hl_def
  have hLspec : ∃ z, Lw a b c l z := Nat.find_spec HL
  set y := Nat.find hLspec with hy_def
  have hLy : Lw a b c l y := Nat.find_spec hLspec
  have lmin : ∀ x < l, ∀ z, ¬ Lw a b c x z := fun x hx z hz => Nat.find_min HL hx ⟨z, hz⟩
  have ymin : ∀ z < y, ¬ Lw a b c l z := fun z hz => Nat.find_min hLspec hz
  set h := Nat.find HH with hh_def
  have hHspec : ∃ z, Hw a b c h z := Nat.find_spec HH
  set w := Nat.find hHspec with hw_def
  have hHw : Hw a b c h w := Nat.find_spec hHspec
  have hmin : ∀ x < h, ∀ z, ¬ Hw a b c x z := fun x hx z hz => Nat.find_min HH hx ⟨z, hz⟩
  have wmin : ∀ z < w, ¬ Hw a b c h z := fun z hz => Nat.find_min hHspec hz
  have hla : l ≤ a := Nat.find_min' HL ⟨0, lw_axis ha hb ⟨b, by ring⟩⟩
  have hha : h ≤ a := Nat.find_min' HH ⟨0, hw_axis ha hc ⟨c, by ring⟩⟩
  obtain ⟨hl1, hyl, hdl⟩ := hLy
  obtain ⟨hh1, hwh, hdh⟩ := hHw
  -- w < l
  have hwl : w < l := by
    by_contra hcon
    push Not at hcon
    rcases Nat.eq_zero_or_pos y with hy0 | hy0
    · apply wmin (w - l) (by omega)
      refine ⟨hh1, ?_, ?_⟩
      · have : (w - l) * b ≤ w * b := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        omega
      · rw [hy0] at hdl
        have e : (h : ℤ) * c - ((w - l : ℕ) : ℤ) * b =
            ((h : ℤ) * c - (w : ℤ) * b) + ((l : ℤ) * b - ((0 : ℕ) : ℤ) * c) := by
          push_cast [Nat.cast_sub hcon]; ring
        rw [e]; exact dvd_add hdh hdl
    · -- (w - l, h - y) is a smaller candidate for h
      have key : ((w - l : ℕ) : ℤ) * b < ((h : ℤ) - y) * c := by
        push_cast [Nat.cast_sub hcon]
        have : (y : ℤ) * c < l * b := by exact_mod_cast hyl
        have : (w : ℤ) * b < h * c := by exact_mod_cast hwh
        nlinarith
      have hyh : y < h := by
        by_contra hyh; push Not at hyh
        have hhy : (h : ℤ) - y ≤ 0 := by
          have : (h : ℤ) ≤ y := by exact_mod_cast hyh
          linarith
        have : ((h : ℤ) - y) * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hhy (by positivity)
        have : (0 : ℤ) ≤ ((w - l : ℕ) : ℤ) * b := by positivity
        linarith
      apply hmin (h - y) (by omega) (w - l)
      refine ⟨by omega, ?_, ?_⟩
      · have : (((w - l) * b : ℕ) : ℤ) < (((h - y) * c : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub hyh.le, Nat.cast_sub hcon] at key ⊢; linarith
        exact_mod_cast this
      · have e : (((h - y : ℕ) : ℤ)) * c - ((w - l : ℕ) : ℤ) * b =
            ((h : ℤ) * c - (w : ℤ) * b) + ((l : ℤ) * b - (y : ℤ) * c) := by
          push_cast [Nat.cast_sub hcon, Nat.cast_sub hyh.le]; ring
        rw [e]; exact dvd_add hdh hdl
  -- y < h
  have hyh : y < h := by
    by_contra hcon
    push Not at hcon
    rcases Nat.eq_zero_or_pos w with hw0 | hw0
    · apply ymin (y - h) (by omega)
      refine ⟨hl1, ?_, ?_⟩
      · have : (y - h) * c ≤ y * c := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        omega
      · rw [hw0] at hdh
        have e : (l : ℤ) * b - ((y - h : ℕ) : ℤ) * c =
            ((l : ℤ) * b - (y : ℤ) * c) + ((h : ℤ) * c - ((0 : ℕ) : ℤ) * b) := by
          push_cast [Nat.cast_sub hcon]; ring
        rw [e]; exact dvd_add hdl hdh
    · apply lmin (l - w) (by omega) (y - h)
      refine ⟨by omega, ?_, ?_⟩
      · have : (((y - h) * c : ℕ) : ℤ) < (((l - w) * b : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub hcon, Nat.cast_sub hwl.le]
          have : (y : ℤ) * c < l * b := by exact_mod_cast hyl
          have : (w : ℤ) * b < h * c := by exact_mod_cast hwh
          nlinarith
        exact_mod_cast this
      · have e : ((l - w : ℕ) : ℤ) * b - ((y - h : ℕ) : ℤ) * c =
            ((l : ℤ) * b - (y : ℤ) * c) + ((h : ℤ) * c - (w : ℤ) * b) := by
          push_cast [Nat.cast_sub hcon, Nat.cast_sub hwl.le]; ring
        rw [e]; exact dvd_add hdl hdh
  -- all four witnesses are lattice vectors; no nonzero lattice point in the L-shape
  have noLat : ∀ i j : ℕ, InR l h w y i j → (a : ℤ) ∣ (i : ℤ) * b + (j : ℤ) * c → i = 0 ∧ j = 0 := by
    intro i j hR hdiv
    obtain ⟨hil, hjh, hcorner⟩ := hR
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · exact ⟨hi0, hj0⟩
      · exfalso
        apply lmin i hil 0
        exact lw_axis hi0 hb (by rw [hj0] at hdiv; simpa using hdiv)
    · rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · exfalso
        apply hmin j hjh 0
        exact hw_axis hj0 hc (by rw [hi0] at hdiv; simpa using hdiv)
      exfalso
      have hyl' : (y : ℤ) * c < l * b := by exact_mod_cast hyl
      have hwh' : (w : ℤ) * b < h * c := by exact_mod_cast hwh
      by_cases hjy : j + y < h
      · -- compare the weight of (i, j) with l b - y c
        rcases lt_trichotomy ((i : ℤ) * b + (j : ℤ) * c) ((l : ℤ) * b - (y : ℤ) * c) with
          hlt | heq | hgt
        · apply lmin (l - i) (by omega) (j + y)
          refine ⟨by omega, ?_, ?_⟩
          · have : (((j + y) * c : ℕ) : ℤ) < (((l - i) * b : ℕ) : ℤ) := by
              push_cast [Nat.cast_sub hil.le]; linarith
            exact_mod_cast this
          · have e : ((l - i : ℕ) : ℤ) * b - ((j + y : ℕ) : ℤ) * c =
                ((l : ℤ) * b - (y : ℤ) * c) - ((i : ℤ) * b + (j : ℤ) * c) := by
              push_cast [Nat.cast_sub hil.le]; ring
            rw [e]; exact dvd_sub hdl hdiv
        · -- equality: c ∣ l - i, impossible
          have e : (((l - i) * b : ℕ) : ℤ) = (((j + y) * c : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub hil.le]; linarith
          have e' : (l - i) * b = (j + y) * c := by exact_mod_cast e
          have hdvd : c ∣ (l - i) * b := ⟨j + y, by rw [e']; ring⟩
          have := Nat.le_of_dvd (by omega) ((Nat.Coprime.symm copbc).dvd_of_dvd_mul_right hdvd)
          omega
        · apply hmin (j + y) hjy (l - i)
          refine ⟨by omega, ?_, ?_⟩
          · have : (((l - i) * b : ℕ) : ℤ) < (((j + y) * c : ℕ) : ℤ) := by
              push_cast [Nat.cast_sub hil.le]; linarith
            exact_mod_cast this
          · have e : ((j + y : ℕ) : ℤ) * c - ((l - i : ℕ) : ℤ) * b =
                ((i : ℤ) * b + (j : ℤ) * c) - ((l : ℤ) * b - (y : ℤ) * c) := by
              push_cast [Nat.cast_sub hil.le]; ring
            rw [e]; exact dvd_sub hdiv hdl
      · have hiw : i + w < l := by
          by_contra hcon; apply hcorner; constructor <;> omega
        rcases lt_trichotomy ((i : ℤ) * b + (j : ℤ) * c) ((h : ℤ) * c - (w : ℤ) * b) with
          hlt | heq | hgt
        · apply hmin (h - j) (by omega) (i + w)
          refine ⟨by omega, ?_, ?_⟩
          · have : (((i + w) * b : ℕ) : ℤ) < (((h - j) * c : ℕ) : ℤ) := by
              push_cast [Nat.cast_sub hjh.le]; linarith
            exact_mod_cast this
          · have e : ((h - j : ℕ) : ℤ) * c - ((i + w : ℕ) : ℤ) * b =
                ((h : ℤ) * c - (w : ℤ) * b) - ((i : ℤ) * b + (j : ℤ) * c) := by
              push_cast [Nat.cast_sub hjh.le]; ring
            rw [e]; exact dvd_sub hdh hdiv
        · have e : (((i + w) * b : ℕ) : ℤ) = (((h - j) * c : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub hjh.le]; linarith
          have e' : (i + w) * b = (h - j) * c := by exact_mod_cast e
          have hdvd : c ∣ (i + w) * b := ⟨h - j, by rw [e']; ring⟩
          have := Nat.le_of_dvd (by omega) ((Nat.Coprime.symm copbc).dvd_of_dvd_mul_right hdvd)
          omega
        · apply lmin (i + w) hiw (h - j)
          refine ⟨by omega, ?_, ?_⟩
          · have : (((h - j) * c : ℕ) : ℤ) < (((i + w) * b : ℕ) : ℤ) := by
              push_cast [Nat.cast_sub hjh.le]; linarith
            exact_mod_cast this
          · have e : ((i + w : ℕ) : ℤ) * b - ((h - j : ℕ) : ℤ) * c =
                ((i : ℤ) * b + (j : ℤ) * c) - ((h : ℤ) * c - (w : ℤ) * b) := by
              push_cast [Nat.cast_sub hjh.le]; ring
            rw [e]; exact dvd_sub hdiv hdh
  -- reduction into the L-shape by the moves (l,-y), (-w,h), (l-w,h-y)
  have red : ∀ s i j : ℕ, i * b + j * c = s → ∃ i' j' m₁ m₂ : ℕ, InR l h w y i' j' ∧
      (i : ℤ) = i' + m₁ * l - m₂ * w ∧ (j : ℤ) = j' + m₂ * h - m₁ * y := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro i j hs
      by_cases hi : l ≤ i
      · obtain ⟨i', j', m₁, m₂, hR, e1, e2⟩ :=
          ih ((i - l) * b + (j + y) * c) (by
            have : i * b = (i - l) * b + l * b := by rw [← Nat.add_mul, Nat.sub_add_cancel hi]
            rw [← hs, this]; nlinarith) (i - l) (j + y) rfl
        refine ⟨i', j', m₁ + 1, m₂, hR, ?_, ?_⟩
        · push_cast [Nat.cast_sub hi] at e1 ⊢; linarith
        · push_cast at e2 ⊢; linarith
      · by_cases hj : h ≤ j
        · obtain ⟨i', j', m₁, m₂, hR, e1, e2⟩ :=
            ih ((i + w) * b + (j - h) * c) (by
              have : j * c = (j - h) * c + h * c := by rw [← Nat.add_mul, Nat.sub_add_cancel hj]
              rw [← hs, this]; nlinarith) (i + w) (j - h) rfl
          refine ⟨i', j', m₁, m₂ + 1, hR, ?_, ?_⟩
          · push_cast at e1 ⊢; linarith
          · push_cast [Nat.cast_sub hj] at e2 ⊢; linarith
        · by_cases hk : l - w ≤ i ∧ h - y ≤ j
          · obtain ⟨hk1, hk2⟩ := hk
            obtain ⟨i', j', m₁, m₂, hR, e1, e2⟩ :=
              ih ((i - (l - w)) * b + (j - (h - y)) * c) (by
                have ei : i * b = (i - (l - w)) * b + (l - w) * b := by
                  rw [← Nat.add_mul, Nat.sub_add_cancel hk1]
                have ej : j * c = (j - (h - y)) * c + (h - y) * c := by
                  rw [← Nat.add_mul, Nat.sub_add_cancel hk2]
                have : 0 < (l - w) * b := Nat.mul_pos (by omega) hb
                rw [← hs, ei, ej]; omega) (i - (l - w)) (j - (h - y)) rfl
            refine ⟨i', j', m₁ + 1, m₂ + 1, hR, ?_, ?_⟩
            · push_cast [Nat.cast_sub hk1, Nat.cast_sub hwl.le] at e1 ⊢; linarith
            · push_cast [Nat.cast_sub hk2, Nat.cast_sub hyh.le] at e2 ⊢; linarith
          · exact ⟨i, j, 0, 0, ⟨by omega, by omega, hk⟩, by simp, by simp⟩
  -- a lattice vector in ℕ² is an integer combination of (l,-y), (-w,h)
  have comb : ∀ i j : ℕ, (a : ℤ) ∣ (i : ℤ) * b + (j : ℤ) * c →
      ∃ m₁ m₂ : ℕ, (i : ℤ) = m₁ * l - m₂ * w ∧ (j : ℤ) = m₂ * h - m₁ * y := by
    intro i j hdiv
    obtain ⟨i', j', m₁, m₂, hR, e1, e2⟩ := red _ i j rfl
    have hdiv' : (a : ℤ) ∣ (i' : ℤ) * b + (j' : ℤ) * c := by
      have e : (i' : ℤ) * b + (j' : ℤ) * c = ((i : ℤ) * b + (j : ℤ) * c) -
          (m₁ : ℤ) * ((l : ℤ) * b - (y : ℤ) * c) - (m₂ : ℤ) * ((h : ℤ) * c - (w : ℤ) * b) := by
        rw [e1, e2]; ring
      rw [e]
      exact dvd_sub (dvd_sub hdiv (dvd_mul_of_dvd_right hdl _)) (dvd_mul_of_dvd_right hdh _)
    obtain ⟨rfl, rfl⟩ := noLat i' j' hR hdiv'
    exact ⟨m₁, m₂, by rw [e1]; ring, by rw [e2]; ring⟩
  -- the determinant
  have hdet : l * h = a + w * y := by
    have hpos : w * y < l * h := Nat.mul_lt_mul_of_lt_of_le hwl hyh.le (by omega)
    set D : ℤ := (l : ℤ) * h - (w : ℤ) * y with hD
    have hDpos : 0 < D := by
      have : ((w * y : ℕ) : ℤ) < ((l * h : ℕ) : ℤ) := by exact_mod_cast hpos
      push_cast at this; linarith
    -- a ∣ D
    have h1 : (a : ℤ) ∣ D := by
      have cop' : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr cop
      apply cop'.dvd_of_dvd_mul_right
      have e : D * b = (h : ℤ) * ((l : ℤ) * b - (y : ℤ) * c) +
          (y : ℤ) * ((h : ℤ) * c - (w : ℤ) * b) := by rw [hD]; ring
      rw [e]; exact dvd_add (dvd_mul_of_dvd_right hdl _) (dvd_mul_of_dvd_right hdh _)
    -- D ∣ a
    have h2 : D ∣ (a : ℤ) := by
      obtain ⟨m₁, m₂, e1, e2⟩ := comb a 0 ⟨b, by ring⟩
      obtain ⟨i₀, hi₀⟩ := exists_mul_modEq ha cop ((a - 1) * c)
      have hdiv0 : (a : ℤ) ∣ (i₀ : ℤ) * b + ((1 : ℕ) : ℤ) * c := by
        have h' := (Int.ModEq.dvd hi₀.symm)
        have e : (i₀ : ℤ) * b + ((1 : ℕ) : ℤ) * c =
            (((i₀ * b : ℕ) : ℤ) - (((a - 1) * c : ℕ) : ℤ)) + (a : ℤ) * c := by
          push_cast [Nat.cast_sub (show 1 ≤ a by omega)]; ring
        rw [e]; exact dvd_add (by simpa using h') (dvd_mul_right _ _)
      obtain ⟨n₁, n₂, f1, f2⟩ := comb i₀ 1 hdiv0
      refine ⟨(m₁ : ℤ) * n₂ - (m₂ : ℤ) * n₁, ?_⟩
      have : (a : ℤ) = (a : ℤ) * ((1 : ℕ) : ℤ) - (i₀ : ℤ) * ((0 : ℕ) : ℤ) := by push_cast; ring
      rw [this, e1, e2, f1, f2, hD]; ring
    have := Int.dvd_antisymm hDpos.le (by positivity) h2 h1
    have : ((l * h : ℕ) : ℤ) = ((a + w * y : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  -- the quotients q₁, q₂
  obtain ⟨q₁, hq₁⟩ := hdl
  obtain ⟨q₂, hq₂⟩ := hdh
  have hapos : (0 : ℤ) < a := by exact_mod_cast ha
  have hq₁pos : 0 < q₁ := by
    have : (y : ℤ) * c < l * b := by exact_mod_cast hyl
    by_contra hneg; push Not at hneg
    have : (a : ℤ) * q₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hapos.le hneg
    linarith
  have hq₂pos : 0 < q₂ := by
    have : (w : ℤ) * b < h * c := by exact_mod_cast hwh
    by_contra hneg; push Not at hneg
    have : (a : ℤ) * q₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hapos.le hneg
    linarith
  refine ⟨l, h, w, y, q₁.toNat, q₂.toNat, ⟨ha, cop, hwl, hyh, hdet, ?_, ?_, by omega, by omega⟩⟩
  · have : ((y * c + a * q₁.toNat : ℕ) : ℤ) = ((l * b : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg hq₁pos.le]; linarith
    exact_mod_cast this
  · have : ((w * b + a * q₂.toNat : ℕ) : ℤ) = ((h * c : ℕ) : ℤ) := by
      push_cast; rw [Int.toNat_of_nonneg hq₂pos.le]; linarith
    exact_mod_cast this

end LShape

end FrobCert
