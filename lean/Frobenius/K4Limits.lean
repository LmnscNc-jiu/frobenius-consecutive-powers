import Frobenius.K4LimitsData
import Frobenius.GenKGrowth

/-!
# Corollary 1.5: lim inf and lim sup of `F(S_n^4)/n^6` and `g(S_n^4)/n^6`

`liminf F/n^6 = 9/5`, `limsup F/n^6 = 26/5`, `liminf g/n^6 = 97/100`, `limsup g/n^6 = 13/5`.

The proof combines Theorem 5.1 for `n ≥ 280` (`frobenius_k4_ge_280`, `genus_k4_ge_280`) with the
polynomial bounds of `K4LimitsData` (uniform bounds for all classes, and sharp bounds on the
classes `n ≡ 15` and `n ≡ 39 (mod 40)`), and an elementary lemma characterising `liminf` and
`limsup` by such bounds.
-/

open Filter FrobCert

namespace FrobK4

/-! ### Two lemmas on `liminf` and `limsup` -/

theorem small_of_pos {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → K / n ≤ ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (K / ε)
  refine ⟨M, fun n hn => ?_⟩
  have hM' : K / ε < n := lt_of_lt_of_le hM (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hK hε.le) hM'
  rw [div_le_iff₀ hnpos]
  rw [div_lt_iff₀ hε] at hM'
  linarith

theorem div_le_self_of_one_le {K : ℝ} (hK : 0 ≤ K) {n : ℕ} (hn : 1 ≤ n) : K / n ≤ K :=
  div_le_self hK (by exact_mod_cast hn)

/-- If `L - K/n ≤ u n ≤ U + K/n` for large `n` and `u n ≤ L + K/n` for infinitely many `n`,
then `liminf u = L`. -/
theorem liminf_eq_of_bounds {u : ℕ → ℝ} {L U K : ℝ} {N : ℕ} (hK : 0 ≤ K)
    (hlo : ∀ n, N ≤ n → L - K / n ≤ u n) (hhi : ∀ n, N ≤ n → u n ≤ U + K / n)
    (hfreq : ∀ m, ∃ n, m ≤ n ∧ u n ≤ L + K / n) : liminf u atTop = L := by
  have hb_le : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (a := U + K) (eventually_atTop.2 ⟨max N 1, fun n hn =>
      (hhi n (le_of_max_le_left hn)).trans (by
        linarith [div_le_self_of_one_le hK (le_of_max_le_right hn)])⟩)
  have hb_ge : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of_eventually_ge (a := L - K) (eventually_atTop.2 ⟨max N 1, fun n hn => by
      linarith [hlo n (le_of_max_le_left hn), div_le_self_of_one_le hK (le_of_max_le_right hn)]⟩)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨M, hM⟩ := small_of_pos hK hε
    apply liminf_le_of_frequently_le _ hb_ge
    rw [frequently_atTop]
    intro a
    obtain ⟨n, hn, hu⟩ := hfreq (max a M)
    exact ⟨n, le_of_max_le_left hn, hu.trans (by linarith [hM n (le_of_max_le_right hn)])⟩
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨M, hM⟩ := small_of_pos hK hε
    have : L - ε ≤ liminf u atTop :=
      le_liminf_of_le hb_le.isCoboundedUnder_ge (eventually_atTop.2 ⟨max N M, fun n hn => by
        linarith [hlo n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)]⟩)
    linarith

/-- If `L - K/n ≤ u n ≤ U + K/n` for large `n` and `U - K/n ≤ u n` for infinitely many `n`,
then `limsup u = U`. -/
theorem limsup_eq_of_bounds {u : ℕ → ℝ} {L U K : ℝ} {N : ℕ} (hK : 0 ≤ K)
    (hlo : ∀ n, N ≤ n → L - K / n ≤ u n) (hhi : ∀ n, N ≤ n → u n ≤ U + K / n)
    (hfreq : ∀ m, ∃ n, m ≤ n ∧ U - K / n ≤ u n) : limsup u atTop = U := by
  have hb_le : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (a := U + K) (eventually_atTop.2 ⟨max N 1, fun n hn =>
      (hhi n (le_of_max_le_left hn)).trans (by
        linarith [div_le_self_of_one_le hK (le_of_max_le_right hn)])⟩)
  have hb_ge : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of_eventually_ge (a := L - K) (eventually_atTop.2 ⟨max N 1, fun n hn => by
      linarith [hlo n (le_of_max_le_left hn), div_le_self_of_one_le hK (le_of_max_le_right hn)]⟩)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨M, hM⟩ := small_of_pos hK hε
    exact limsup_le_of_le hb_ge.isCoboundedUnder_le (eventually_atTop.2 ⟨max N M, fun n hn => by
      linarith [hhi n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)]⟩)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨M, hM⟩ := small_of_pos hK hε
    have : U - ε ≤ limsup u atTop := by
      apply le_limsup_of_frequently_le _ hb_le
      rw [frequently_atTop]
      intro a
      obtain ⟨n, hn, hu⟩ := hfreq (max a M)
      exact ⟨n, le_of_max_le_left hn, le_trans (by linarith [hM n (le_of_max_le_right hn)]) hu⟩
    linarith

/-! ### From integer bounds to bounds for `v / n^6` -/

theorem lo_real {A c K : ℝ} {v : ℝ} {n : ℕ} (hn : 1 ≤ n) (hc : 0 < c)
    (h : A * (n : ℝ) ^ 6 - K * (n : ℝ) ^ 5 ≤ c * v) : A / c - (K / c) / n ≤ v / (n : ℝ) ^ 6 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (A / c - (K / c) / n) * (n : ℝ) ^ 6 = (A * (n : ℝ) ^ 6 - K * (n : ℝ) ^ 5) / c := by
    field_simp
  rw [le_div_iff₀ (by positivity), e, div_le_iff₀ hc]
  linarith

theorem hi_real {A c K : ℝ} {v : ℝ} {n : ℕ} (hn : 1 ≤ n) (hc : 0 < c)
    (h : c * v ≤ A * (n : ℝ) ^ 6 + K * (n : ℝ) ^ 5) : v / (n : ℝ) ^ 6 ≤ A / c + (K / c) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (A / c + (K / c) / n) * (n : ℝ) ^ 6 = (A * (n : ℝ) ^ 6 + K * (n : ℝ) ^ 5) / c := by
    field_simp
  rw [div_le_iff₀ (by positivity), e, le_div_iff₀ hc]
  linarith

/-! ### Corollary 1.5 -/

/-- A Frobenius-number function for `S_n^4` exists (for `n ≥ 2`). -/
theorem exists_frob_fun : ∃ F : ℕ → ℕ, ∀ n, 2 ≤ n → FrobeniusNumber (F n) (gens n) := by
  choose F hF using fun n : ℕ => (fun h : 2 ≤ n => GenK.exists_frobenius (k := 4) (by norm_num) h)
  refine ⟨fun n => if h : 2 ≤ n then F n h else 0, fun n hn => ?_⟩
  simp only [hn, dite_true]
  exact hF n hn

/-- integer bounds `A n^6 - K n^5 ≤ c v` give `A/c - (K/c)/n ≤ v/n^6` -/
theorem real_lo {A K c v : ℤ} {n : ℕ} (hn : 1 ≤ n) (hc : 0 < c)
    (h : A * (n : ℤ) ^ 6 - K * (n : ℤ) ^ 5 ≤ c * v) :
    (A : ℝ) / c - ((K : ℝ) / c) / n ≤ (v : ℝ) / (n : ℝ) ^ 6 :=
  lo_real hn (by exact_mod_cast hc) (by exact_mod_cast h)

/-- integer bounds `c v ≤ A n^6 + K n^5` give `v/n^6 ≤ A/c + (K/c)/n` -/
theorem real_hi {A K c v : ℤ} {n : ℕ} (hn : 1 ≤ n) (hc : 0 < c)
    (h : c * v ≤ A * (n : ℤ) ^ 6 + K * (n : ℤ) ^ 5) :
    (v : ℝ) / (n : ℝ) ^ 6 ≤ (A : ℝ) / c + ((K : ℝ) / c) / n :=
  hi_real hn (by exact_mod_cast hc) (by exact_mod_cast h)

section
variable {F : ℕ → ℕ} (hF : ∀ n, 2 ≤ n → FrobeniusNumber (F n) (gens n))
include hF

theorem frob_cast {n : ℕ} (hn : 280 ≤ n) : (F n : ℝ) = ((Phi n : ℤ) : ℝ) := by
  rw [← (frobenius_k4_ge_280 n hn (F n)).mp (hF n (by omega))]; push_cast; ring

theorem F_lo {n : ℕ} (hn : 280 ≤ n) : 9 / 5 - ((KF : ℝ) / 5) / n ≤ (F n : ℝ) / (n : ℝ) ^ 6 := by
  have h := real_lo (c := 5) (by omega) (by norm_num) (Phi_lo n (by omega))
  rw [← frob_cast hF hn] at h
  simpa using h

theorem F_hi {n : ℕ} (hn : 280 ≤ n) : (F n : ℝ) / (n : ℝ) ^ 6 ≤ 26 / 5 + ((KF : ℝ) / 5) / n := by
  have h := real_hi (c := 5) (by omega) (by norm_num) (Phi_hi n (by omega))
  rw [← frob_cast hF hn] at h
  simpa using h

theorem F_sharp15 {n : ℕ} (hn : 280 ≤ n) (hr : n % 40 = 15) :
    (F n : ℝ) / (n : ℝ) ^ 6 ≤ 9 / 5 + ((KF : ℝ) / 5) / n := by
  have e : Phi n = phi15 n := by simp only [Phi, hr]
  have h0 := phi15_sharp (n : ℤ) (by exact_mod_cast (show 1 ≤ n by omega))
  rw [← e] at h0
  have h := real_hi (c := 5) (by omega) (by norm_num) h0
  rw [← frob_cast hF hn] at h
  simpa using h

theorem F_sharp39 {n : ℕ} (hn : 280 ≤ n) (hr : n % 40 = 39) :
    26 / 5 - ((KF : ℝ) / 5) / n ≤ (F n : ℝ) / (n : ℝ) ^ 6 := by
  have e : Phi n = phi39 n := by simp only [Phi, hr]
  have h0 := phi39_sharp (n : ℤ) (by exact_mod_cast (show 1 ≤ n by omega))
  rw [← e] at h0
  have h := real_lo (c := 5) (by omega) (by norm_num) h0
  rw [← frob_cast hF hn] at h
  simpa using h

end

theorem genus_cast {n : ℕ} (hn : 280 ≤ n) : (genus (gens n) : ℝ) = ((Gam n : ℤ) : ℝ) := by
  rw [← genus_k4_ge_280 n hn]; push_cast; ring

theorem G_lo {n : ℕ} (hn : 280 ≤ n) :
    97 / 100 - ((KG : ℝ) / 100) / n ≤ (genus (gens n) : ℝ) / (n : ℝ) ^ 6 := by
  have h := real_lo (c := 100) (by omega) (by norm_num) (Gam_lo n (by omega))
  rw [← genus_cast hn] at h
  simpa using h

theorem G_hi {n : ℕ} (hn : 280 ≤ n) :
    (genus (gens n) : ℝ) / (n : ℝ) ^ 6 ≤ 13 / 5 + ((KG : ℝ) / 5) / n := by
  have h := real_hi (c := 5) (by omega) (by norm_num) (Gam_hi n (by omega))
  rw [← genus_cast hn] at h
  simpa using h

theorem G_sharp15 {n : ℕ} (hn : 280 ≤ n) (hr : n % 40 = 15) :
    (genus (gens n) : ℝ) / (n : ℝ) ^ 6 ≤ 97 / 100 + ((KG : ℝ) / 100) / n := by
  have e : Gam n = gam15 n := by simp only [Gam, hr]
  have h0 := gam15_sharp (n : ℤ) (by exact_mod_cast (show 1 ≤ n by omega))
  rw [← e] at h0
  have h := real_hi (c := 100) (by omega) (by norm_num) h0
  rw [← genus_cast hn] at h
  simpa using h

theorem G_sharp39 {n : ℕ} (hn : 280 ≤ n) (hr : n % 40 = 39) :
    13 / 5 - ((KG : ℝ) / 5) / n ≤ (genus (gens n) : ℝ) / (n : ℝ) ^ 6 := by
  have e : Gam n = gam39 n := by simp only [Gam, hr]
  have h0 := gam39_sharp (n : ℤ) (by exact_mod_cast (show 1 ≤ n by omega))
  rw [← e] at h0
  have h := real_lo (c := 5) (by omega) (by norm_num) h0
  rw [← genus_cast hn] at h
  simpa using h

/-- **Corollary 1.5.** For any choice of the Frobenius numbers `F n` of `S_n^4` (`n ≥ 2`),
`liminf F(n)/n^6 = 9/5`, `limsup F(n)/n^6 = 26/5`, and for the genus
`liminf g(n)/n^6 = 97/100`, `limsup g(n)/n^6 = 13/5`. Such a choice exists by
`exists_frob_fun`, and it is unique for `n ≥ 2`. -/
theorem cor_limits {F : ℕ → ℕ} (hF : ∀ n, 2 ≤ n → FrobeniusNumber (F n) (gens n)) :
    liminf (fun n => (F n : ℝ) / (n : ℝ) ^ 6) atTop = 9 / 5 ∧
    limsup (fun n => (F n : ℝ) / (n : ℝ) ^ 6) atTop = 26 / 5 ∧
    liminf (fun n => (genus (gens n) : ℝ) / (n : ℝ) ^ 6) atTop = 97 / 100 ∧
    limsup (fun n => (genus (gens n) : ℝ) / (n : ℝ) ^ 6) atTop = 13 / 5 := by
  have hKF : (0 : ℝ) ≤ (KF : ℝ) / 5 := by simp only [KF]; norm_num
  have hKG : (0 : ℝ) ≤ (KG : ℝ) / 5 := by simp only [KG]; norm_num
  have hKG100 : ∀ n : ℕ, ((KG : ℝ) / 100) / n ≤ ((KG : ℝ) / 5) / n := fun n =>
    div_le_div_of_nonneg_right (by simp only [KG]; norm_num) (Nat.cast_nonneg _)
  have Glo' : ∀ n, 280 ≤ n →
      97 / 100 - ((KG : ℝ) / 5) / n ≤ (genus (gens n) : ℝ) / (n : ℝ) ^ 6 := fun n hn =>
    le_trans (by linarith [hKG100 n]) (G_lo hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine liminf_eq_of_bounds (U := 26 / 5) (N := 280) hKF (fun n hn => F_lo hF hn)
      (fun n hn => F_hi hF hn) (fun m => ⟨40 * (m + 7) + 15, by omega, ?_⟩)
    exact F_sharp15 hF (by omega) (by omega)
  · refine limsup_eq_of_bounds (L := 9 / 5) (N := 280) hKF (fun n hn => F_lo hF hn)
      (fun n hn => F_hi hF hn) (fun m => ⟨40 * (m + 7) + 39, by omega, ?_⟩)
    exact F_sharp39 hF (by omega) (by omega)
  · refine liminf_eq_of_bounds (U := 13 / 5) (N := 280) hKG Glo' (fun n hn => G_hi hn)
      (fun m => ⟨40 * (m + 7) + 15, by omega, ?_⟩)
    exact (G_sharp15 (by omega) (by omega)).trans (by linarith [hKG100 (40 * (m + 7) + 15)])
  · refine limsup_eq_of_bounds (L := 97 / 100) (N := 280) hKG Glo' (fun n hn => G_hi hn)
      (fun m => ⟨40 * (m + 7) + 39, by omega, ?_⟩)
    exact G_sharp39 (by omega) (by omega)

/-- In particular `F(S_n^4)/n^6` has no limit. -/
theorem no_limit {F : ℕ → ℕ} (hF : ∀ n, 2 ≤ n → FrobeniusNumber (F n) (gens n)) :
    liminf (fun n => (F n : ℝ) / (n : ℝ) ^ 6) atTop <
      limsup (fun n => (F n : ℝ) / (n : ℝ) ^ 6) atTop := by
  obtain ⟨h1, h2, -, -⟩ := cor_limits hF
  rw [h1, h2]; norm_num

end FrobK4
