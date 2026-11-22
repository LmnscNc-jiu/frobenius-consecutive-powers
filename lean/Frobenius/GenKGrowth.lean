import Frobenius.GenKLattice
import Frobenius.LShape

/-!
# Theorem 1.1: the order of growth of the Frobenius number and the genus

For `0 < p < q`, `k ≥ 2` and `e = k + ⌈k/2⌉` there are constants `c, C` such that for all `n ≥ 2`
with `gcd(n, p, q) = 1` the Frobenius number `F` of `⟨n^k, (n+p)^k, (n+q)^k⟩` exists and
`n^e ≤ c F`, `F ≤ C n^e`, `n^e ≤ 2 c g`, `g ≤ C n^e` (`g` the genus) (`growthPQ`).  The case of
three consecutive `k`-th powers, `S_n^k`, is `(p, q) = (1, 2)` (`growth`).

Both bounds come from two lemmas valid for any `⟨a, b, c⟩` with `gcd(a, b, c) = 1`:
* `rep_of_box` (upper bound): if the relation lattice contains two independent vectors of sup norm
  `≤ R`, every residue class modulo `a` contains `i b + j c` with `0 ≤ i, j ≤ 4R`, hence every
  `x ≥ 4R (b + c)` lies in the semigroup;
* `short_vectors_of_frob` (lower bound): the integers `F + 1, …, F + a` lie in the semigroup, so
  every residue class contains `i b + j c` with `0 ≤ i, j ≤ X = ⌊(F + a)/b⌋`, and the lattice
  contains two independent vectors of sup norm `≤ 2X + 1`.
Combined with the second successive minimum of Theorem 1.2 (`lattice_minima`) they give
`F ≍ n^e`.  The genus satisfies `(F + 1)/2 ≤ g ≤ F` (`genus_le`, `frob_succ_le_two_genus`).
-/

open FrobCert

namespace GenK

open Classical

/-- The generators of `S_n^k`. -/
abbrev gensK (k n : ℕ) : Set ℕ := {n ^ k, (n + 1) ^ k, (n + 2) ^ k}

/-! ### Genus versus Frobenius number (any numerical semigroup) -/

theorem gap_le {s : Set ℕ} {F x : ℕ} (hF : FrobeniusNumber F s)
    (hx : x ∉ AddSubmonoid.closure s) : x ≤ F := hF.2 hx

theorem genus_eq_card {s : Set ℕ} {F : ℕ} (hF : FrobeniusNumber F s) :
    genus s = ((Finset.range (F + 1)).filter (fun x => x ∉ AddSubmonoid.closure s)).card := by
  rw [genus, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  constructor
  · intro hx; exact ⟨Nat.lt_succ_of_le (gap_le hF hx), hx⟩
  · exact fun h => h.2

/-- `g ≤ F`. -/
theorem genus_le {s : Set ℕ} {F : ℕ} (hF : FrobeniusNumber F s) : genus s ≤ F := by
  rw [genus_eq_card hF]
  have hsub : (Finset.range (F + 1)).filter (fun x => x ∉ AddSubmonoid.closure s) ⊆
      (Finset.range (F + 1)).erase 0 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hx.1⟩
    rintro rfl; exact hx.2 (AddSubmonoid.zero_mem _)
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem (by simp), Finset.card_range]; omega

/-- `F + 1 ≤ 2 g`: at most one of `x`, `F - x` lies in the semigroup. -/
theorem frob_succ_le_two_genus {s : Set ℕ} {F : ℕ} (hF : FrobeniusNumber F s) :
    F + 1 ≤ 2 * genus s := by
  rw [genus_eq_card hF]
  set G := (Finset.range (F + 1)).filter (fun x => x ∉ AddSubmonoid.closure s)
  set N := (Finset.range (F + 1)).filter (fun x => ¬ (x ∉ AddSubmonoid.closure s))
  have htot : G.card + N.card = F + 1 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hNG : N.card ≤ G.card := by
    apply Finset.card_le_card_of_injOn (fun x => F - x)
    · intro x hx
      simp only [N, Finset.coe_filter, Finset.mem_range, not_not, Set.mem_ofPred_eq] at hx
      simp only [G, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      refine ⟨by omega, fun hFx => hF.1 ?_⟩
      have := add_mem hx.2 hFx
      rwa [Nat.add_sub_cancel' (by omega)] at this
    · intro x hx x' hx' hxx
      simp only [N, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hx'
      simp only at hxx
      omega
  omega

/-! ### Arithmetic of the generators -/

theorem coprime_ab (k n : ℕ) : Nat.Coprime (n ^ k) ((n + 1) ^ k) :=
  Nat.Coprime.pow _ _ (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n))

theorem coprime_bc (k n : ℕ) : Nat.Coprime ((n + 1) ^ k) ((n + 2) ^ k) := by
  apply Nat.Coprime.pow
  have : n + 2 = (n + 1) + 1 := by ring
  rw [this]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)

theorem a_lt_b {k n : ℕ} (hk : 1 ≤ k) : n ^ k < (n + 1) ^ k :=
  Nat.pow_lt_pow_left (by omega) (by omega)

theorem b_lt_c {k n : ℕ} (hk : 1 ≤ k) : (n + 1) ^ k < (n + 2) ^ k :=
  Nat.pow_lt_pow_left (by omega) (by omega)

theorem two_le_a {k n : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) : 2 ≤ n ^ k :=
  le_trans (by simpa using hn) (Nat.pow_le_pow_right (by omega) hk : n ^ 1 ≤ n ^ k)

/-- An L-shaped certificate for `S_n^k`. -/
theorem cert_k {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∃ l h w y q₁ q₂, Cert (n ^ k) ((n + 1) ^ k) ((n + 2) ^ k) l h w y q₁ q₂ :=
  exists_cert (by positivity) (by positivity) ((a_lt_b hk).trans (b_lt_c hk)) (coprime_ab k n)
    (coprime_bc k n)

/-- The corner value `M` of a certificate is at least `a`. -/
theorem a_le_M {a b c l h w y q₁ q₂ : ℕ} (C : Cert a b c l h w y q₁ q₂) (ha2 : 2 ≤ a)
    (hab : a < b) (hac : a < c) :
    a ≤ max ((l - 1) * b + (h - y - 1) * c) ((l - w - 1) * b + (h - 1) * c) := by
  have hw := C.hw; have hy := C.hy; have hdet := C.det
  by_cases hl : 2 ≤ l
  · apply le_max_of_le_left
    have : b ≤ (l - 1) * b := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have hl1 : l = 1 := by omega
    have hw0 : w = 0 := by omega
    rw [hl1, hw0] at hdet
    have hh : a = h := by simpa using hdet.symm
    apply le_max_of_le_right
    have : c ≤ (h - 1) * c := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- **Existence** of the Frobenius number of `S_n^k` (`n ≥ 2`, `k ≥ 1`). -/
theorem exists_frobenius {k n : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ∃ F, FrobeniusNumber F (gensK k n) := by
  obtain ⟨l, h, w, y, q₁, q₂, C⟩ := cert_k hk (by omega : 1 ≤ n)
  exact ⟨_, frobenius_of_cert C (a_le_M C (two_le_a hk hn) (a_lt_b hk)
    ((a_lt_b hk).trans (b_lt_c hk)))⟩

theorem frobeniusNumber_unique {F G : ℕ} {s : Set ℕ} (hF : FrobeniusNumber F s)
    (hG : FrobeniusNumber G s) : F = G :=
  IsGreatest.unique hF hG

theorem one_le_frob {k n F : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) (hF : FrobeniusNumber F (gensK k n)) :
    1 ≤ F := by
  apply hF.2
  simp only [Set.mem_ofPred_eq, mem_closure_iff]
  rintro ⟨α, i, j, hrep⟩
  have ha := two_le_a hk hn
  have hb : 2 ≤ (n + 1) ^ k := ha.trans (a_lt_b hk).le
  have hc : 2 ≤ (n + 2) ^ k := hb.trans (b_lt_c hk).le
  rcases Nat.eq_zero_or_pos α with h1 | h1
  · rcases Nat.eq_zero_or_pos i with h2 | h2
    · rcases Nat.eq_zero_or_pos j with h3 | h3
      · subst h1 h2 h3; simp at hrep
      · have : 2 ≤ j * (n + 2) ^ k := le_trans hc (Nat.le_mul_of_pos_left _ h3)
        omega
    · have : 2 ≤ i * (n + 1) ^ k := le_trans hb (Nat.le_mul_of_pos_left _ h2)
      omega
  · have : 2 ≤ α * n ^ k := le_trans ha (Nat.le_mul_of_pos_left _ h1)
    omega

/-! ### Helper lemmas -/

theorem abs_le_of_supn {u : ℤ × ℤ} {R : ℕ} (h : supn u ≤ R) : |u.1| ≤ R ∧ |u.2| ≤ R := by
  simp only [supn] at h
  constructor
  · rw [← Int.natCast_natAbs]; exact_mod_cast (le_max_left _ _).trans h
  · rw [← Int.natCast_natAbs]; exact_mod_cast (le_max_right _ _).trans h

/-- reduction of one coordinate into `[-2R, 2R]` -/
theorem coord_bound {D r₁ r₂ u₁ v₁ z : ℤ} {R : ℕ} (hD : D ≠ 0) (hr₁ : 0 ≤ r₁) (hr₁' : r₁ < |D|)
    (hr₂ : 0 ≤ r₂) (hr₂' : r₂ < |D|) (hu : |u₁| ≤ R) (hv : |v₁| ≤ R)
    (hz : D * z = r₁ * u₁ + r₂ * v₁) : |z| ≤ 2 * R := by
  have hDpos : 0 < |D| := abs_pos.mpr hD
  have h1 : |D| * |z| ≤ |D| * (2 * R) := by
    rw [← abs_mul, hz]
    calc |r₁ * u₁ + r₂ * v₁| ≤ |r₁ * u₁| + |r₂ * v₁| := abs_add_le _ _
      _ = r₁ * |u₁| + r₂ * |v₁| := by rw [abs_mul, abs_mul, abs_of_nonneg hr₁, abs_of_nonneg hr₂]
      _ ≤ r₁ * R + r₂ * R := by gcongr
      _ ≤ |D| * R + |D| * R := by
          have : (0 : ℤ) ≤ R := by positivity
          gcongr
      _ = |D| * (2 * R) := by ring
  exact le_of_mul_le_mul_left h1 hDpos

/-! ### Two lemmas for an arbitrary three-generated semigroup `⟨a, b, c⟩` -/

/-- `u` lies in the relation lattice of `(a; b, c)`. -/
def InLabc (a b c : ℕ) (u : ℤ × ℤ) : Prop := (a : ℤ) ∣ u.1 * b + u.2 * c

/-- **Box lemma.** Assume `x a + y b + z c = 1` for some integers. If the relation lattice of
`(a; b, c)` contains two independent vectors of sup norm `≤ R`, then every
`x ≥ 4R (b + c)` lies in `⟨a, b, c⟩`. -/
theorem rep_of_box {a b c : ℕ} (ha : 0 < a) (hbez : ∃ α β γ : ℤ, α * a + β * b + γ * c = 1)
    {u v : ℤ × ℤ} (hu : InLabc a b c u) (hv : InLabc a b c v) (huv : detZ u v ≠ 0) {R : ℕ}
    (hRu : supn u ≤ R) (hRv : supn v ≤ R) (x : ℕ) (hx : 4 * R * (b + c) ≤ x) : Rep a b c x := by
  obtain ⟨α, β, γ, hαβγ⟩ := hbez
  set i₀ : ℤ := (x : ℤ) * β
  set j₀ : ℤ := (x : ℤ) * γ
  set D := detZ u v
  set y : ℤ × ℤ := (i₀ - 2 * R, j₀ - 2 * R)
  set s := detZ y v
  set t := detZ u y
  have hs := Int.mul_ediv_add_emod s D
  have ht := Int.mul_ediv_add_emod t D
  set q₁ := s / D
  set q₂ := t / D
  set r₁ := s % D
  set r₂ := t % D
  have hr₁ : 0 ≤ r₁ := Int.emod_nonneg _ huv
  have hr₂ : 0 ≤ r₂ := Int.emod_nonneg _ huv
  have hr₁' : r₁ < |D| := Int.emod_lt_abs _ huv
  have hr₂' : r₂ < |D| := Int.emod_lt_abs _ huv
  obtain ⟨hu1, hu2⟩ := abs_le_of_supn hRu
  obtain ⟨hv1, hv2⟩ := abs_le_of_supn hRv
  set z₁ := y.1 - q₁ * u.1 - q₂ * v.1
  set z₂ := y.2 - q₁ * u.2 - q₂ * v.2
  have hz₁ : D * z₁ = r₁ * u.1 + r₂ * v.1 := by
    have e : D * y.1 = s * u.1 + t * v.1 := by simp only [D, s, t, detZ]; ring
    have : D * z₁ = D * y.1 - (D * q₁) * u.1 - (D * q₂) * v.1 := by simp only [z₁]; ring
    rw [this, e]; linear_combination (-u.1) * hs - v.1 * ht
  have hz₂ : D * z₂ = r₁ * u.2 + r₂ * v.2 := by
    have e : D * y.2 = s * u.2 + t * v.2 := by simp only [D, s, t, detZ]; ring
    have : D * z₂ = D * y.2 - (D * q₁) * u.2 - (D * q₂) * v.2 := by simp only [z₂]; ring
    rw [this, e]; linear_combination (-u.2) * hs - v.2 * ht
  have hb₁ := abs_le.mp (coord_bound huv hr₁ hr₁' hr₂ hr₂' hu1 hv1 hz₁)
  have hb₂ := abs_le.mp (coord_bound huv hr₁ hr₁' hr₂ hr₂' hu2 hv2 hz₂)
  set P₁ := z₁ + 2 * R
  set P₂ := z₂ + 2 * R
  have hP₁ : 0 ≤ P₁ ∧ P₁ ≤ 4 * R := ⟨by linarith [hb₁.1], by linarith [hb₁.2]⟩
  have hP₂ : 0 ≤ P₂ ∧ P₂ ≤ 4 * R := ⟨by linarith [hb₂.1], by linarith [hb₂.2]⟩
  have hPeq : P₁ * b + P₂ * c = i₀ * b + j₀ * c - q₁ * (u.1 * b + u.2 * c) -
      q₂ * (v.1 * b + v.2 * c) := by
    simp only [P₁, P₂, z₁, z₂, y]; ring
  have hdx : (a : ℤ) ∣ (x : ℤ) - (P₁ * b + P₂ * c) := by
    rw [hPeq]
    have e : (x : ℤ) - (i₀ * b + j₀ * c - q₁ * (u.1 * b + u.2 * c) - q₂ * (v.1 * b + v.2 * c)) =
        ((x : ℤ) * α) * a + q₁ * (u.1 * b + u.2 * c) + q₂ * (v.1 * b + v.2 * c) := by
      simp only [i₀, j₀]; linear_combination (-(x : ℤ)) * hαβγ
    rw [e]
    exact dvd_add (dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right hu _))
      (dvd_mul_of_dvd_right hv _)
  obtain ⟨m, hm⟩ := hdx
  have hxbig : (4 * R * (b + c) : ℤ) ≤ x := by exact_mod_cast hx
  have hPw : P₁ * b + P₂ * c ≤ 4 * R * (b + c) := by
    have hb0 : (0 : ℤ) ≤ b := by positivity
    have hc0 : (0 : ℤ) ≤ c := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hP₁.2 hb0, mul_le_mul_of_nonneg_right hP₂.2 hc0]
  have hm0 : 0 ≤ m := by
    have hapos : (0 : ℤ) < a := by exact_mod_cast ha
    by_contra hneg; push Not at hneg
    have : (a : ℤ) * m < 0 := mul_neg_of_pos_of_neg hapos hneg
    linarith
  refine ⟨m.toNat, P₁.toNat, P₂.toNat, ?_⟩
  have : (x : ℤ) = (m.toNat : ℤ) * a + (P₁.toNat : ℤ) * b + (P₂.toNat : ℤ) * c := by
    rw [Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hP₁.1, Int.toNat_of_nonneg hP₂.1]
    linear_combination hm
  exact_mod_cast this

/-- **Covering lemma.** If `F` is the Frobenius number of `⟨a, b, c⟩` with `0 < b ≤ c`, then every
residue class of `ℤ²` modulo the relation lattice meets `[0, X]²`, `X = ⌊(F + a)/b⌋`. -/
theorem class_in_box {a b c F : ℕ} (ha : 0 < a) (hb : 0 < b) (hbc : b ≤ c)
    (hF : FrobeniusNumber F {a, b, c}) (t : ℤ) :
    ∃ i j : ℕ, i ≤ (F + a) / b ∧ j ≤ (F + a) / b ∧ (a : ℤ) ∣ t - (i * b + j * c) := by
  have hapos : (0 : ℤ) < a := by exact_mod_cast ha
  set r : ℤ := (t - (F + 1)) % a
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hapos.ne'
  have hra : r < a := Int.emod_lt_of_pos _ hapos
  set m : ℕ := F + 1 + r.toNat
  have hm : (m : ℤ) = F + 1 + r := by simp only [m]; push_cast; rw [Int.toNat_of_nonneg hr0]
  have hmS : m ∈ AddSubmonoid.closure ({a, b, c} : Set ℕ) := by
    by_contra hcon; have := hF.2 hcon; omega
  rw [mem_closure_iff] at hmS
  obtain ⟨α, i, j, hrep⟩ := hmS
  have hmle : m ≤ F + a := by
    have : r.toNat < a := by omega
    omega
  have hib : i * b ≤ F + a := by
    have : i * b ≤ m := by rw [hrep]; omega
    omega
  have hjc : j * b ≤ F + a := by
    have h1 : j * c ≤ m := by rw [hrep]; omega
    have h2 : j * b ≤ j * c := Nat.mul_le_mul_left _ hbc
    omega
  refine ⟨i, j, (Nat.le_div_iff_mul_le hb).mpr hib, (Nat.le_div_iff_mul_le hb).mpr hjc, ?_⟩
  have e1 : (a : ℤ) ∣ t - m := by
    rw [hm]
    have h := Int.mul_ediv_add_emod (t - (F + 1)) (a : ℤ)
    exact ⟨(t - (F + 1)) / a, by linarith⟩
  have e2 : t - (i * b + j * c : ℕ) = (t - m) + α * a := by
    have : (m : ℤ) = α * a + i * b + j * c := by exact_mod_cast hrep
    push_cast; linarith
  have e2' : t - ((i : ℤ) * b + (j : ℤ) * c) = (t - m) + α * a := by
    have := e2; push_cast at this; exact this
  rw [e2']
  exact dvd_add e1 (dvd_mul_left _ _)

/-- Two independent short vectors from the Frobenius number. -/
theorem short_vectors_of_frob {a b c F : ℕ} (ha : 0 < a) (hb : 0 < b) (hbc : b ≤ c)
    (hF : FrobeniusNumber F {a, b, c}) :
    ∃ u v : ℤ × ℤ, InLabc a b c u ∧ InLabc a b c v ∧ detZ u v ≠ 0 ∧
      supn u ≤ 2 * ((F + a) / b) + 1 ∧ supn v ≤ 2 * ((F + a) / b) + 1 := by
  set X := (F + a) / b
  obtain ⟨i, j, hi, hj, h1⟩ := class_in_box ha hb hbc hF ((2 * X + 1 : ℕ) * (b : ℤ))
  obtain ⟨i', j', hi', hj', h2⟩ := class_in_box ha hb hbc hF ((2 * X + 1 : ℕ) * (c : ℤ))
  refine ⟨((2 * X + 1 : ℕ) - (i : ℤ), -(j : ℤ)), (-(i' : ℤ), (2 * X + 1 : ℕ) - (j' : ℤ)),
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold InLabc
    have e : ((2 * X + 1 : ℕ) - (i : ℤ)) * b + -(j : ℤ) * c =
        ((2 * X + 1 : ℕ) * (b : ℤ)) - (i * b + j * c) := by ring
    simp only; rw [e]; exact h1
  · unfold InLabc
    have e : -(i' : ℤ) * b + ((2 * X + 1 : ℕ) - (j' : ℤ)) * c =
        ((2 * X + 1 : ℕ) * (c : ℤ)) - (i' * b + j' * c) := by ring
    simp only; rw [e]; exact h2
  · simp only [detZ]
    have hi'' : (i : ℤ) ≤ X := by exact_mod_cast hi
    have hj'' : (j : ℤ) ≤ X := by exact_mod_cast hj
    have hi3 : (i' : ℤ) ≤ X := by exact_mod_cast hi'
    have hj3 : (j' : ℤ) ≤ X := by exact_mod_cast hj'
    have h0i : (0 : ℤ) ≤ i := by positivity
    have h0j : (0 : ℤ) ≤ j := by positivity
    have h0i' : (0 : ℤ) ≤ i' := by positivity
    have h0j' : (0 : ℤ) ≤ j' := by positivity
    push_cast
    nlinarith [mul_le_mul hi3 hj'' h0j (by positivity : (0 : ℤ) ≤ X)]
  · simp only [supn]
    apply max_le
    · have : (i : ℤ) ≤ X := by exact_mod_cast hi
      have h : ((2 * X + 1 : ℕ) - (i : ℤ)).natAbs = 2 * X + 1 - i := by
        rw [show ((2 * X + 1 : ℕ) - (i : ℤ)) = ((2 * X + 1 - i : ℕ) : ℤ) by push_cast [show i ≤ 2 * X + 1 by omega]; ring]
        exact Int.natAbs_natCast _
      rw [h]; omega
    · simp only [Int.natAbs_neg, Int.natAbs_natCast]; omega
  · simp only [supn]
    apply max_le
    · simp only [Int.natAbs_neg, Int.natAbs_natCast]; omega
    · have h : ((2 * X + 1 : ℕ) - (j' : ℤ)).natAbs = 2 * X + 1 - j' := by
        rw [show ((2 * X + 1 : ℕ) - (j' : ℤ)) = ((2 * X + 1 - j' : ℕ) : ℤ) by push_cast [show j' ≤ 2 * X + 1 by omega]; ring]
        exact Int.natAbs_natCast _
      rw [h]; omega

/-! ### Theorem 1.1 for `⟨n^k, (n+p)^k, (n+q)^k⟩` -/

/-- The generators of `⟨n^k, (n+p)^k, (n+q)^k⟩`. -/
abbrev gensPQ (p q k n : ℕ) : Set ℕ := {n ^ k, (n + p) ^ k, (n + q) ^ k}

theorem inL_iff {p q k n : ℕ} (u : ℤ × ℤ) :
    InL p q k n u ↔ InLabc (n ^ k) ((n + p) ^ k) ((n + q) ^ k) u := by
  simp only [InL, InLabc]; push_cast; rfl

theorem bezout_abc {p q k n : ℕ} (hg : Nat.gcd n (Nat.gcd p q) = 1) :
    ∃ α β γ : ℤ, α * ((n ^ k : ℕ) : ℤ) + β * (((n + p) ^ k : ℕ) : ℤ) + γ * (((n + q) ^ k : ℕ) : ℤ) = 1 := by
  obtain ⟨x, y, z, h⟩ := bezout3 (k := k) hg
  exact ⟨x, y, z, by push_cast; exact h⟩

/-- The Frobenius number exists as soon as all large integers are representable. -/
theorem exists_frob_of_rep {s : Set ℕ} {M : ℕ} (h1 : 1 ∉ AddSubmonoid.closure s)
    (hM : ∀ x, M ≤ x → x ∈ AddSubmonoid.closure s) : ∃ F, FrobeniusNumber F s := by
  have hne : ({x | x ∉ AddSubmonoid.closure s} : Set ℕ).Nonempty := ⟨1, h1⟩
  have hbdd : BddAbove ({x | x ∉ AddSubmonoid.closure s} : Set ℕ) := by
    refine ⟨M, fun x hx => ?_⟩
    by_contra hlt; push Not at hlt; exact hx (hM x hlt.le)
  exact ⟨sSup {x | x ∉ AddSubmonoid.closure s}, Nat.sSup_mem hne hbdd,
    fun x hx => le_csSup hbdd hx⟩

theorem one_not_mem {p q k n : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) :
    1 ∉ AddSubmonoid.closure (gensPQ p q k n) := by
  rw [mem_closure_iff]
  rintro ⟨α, i, j, hrep⟩
  have ha := two_le_a hk hn
  have hb : 2 ≤ (n + p) ^ k := ha.trans (Nat.pow_le_pow_left (by omega) k)
  have hc : 2 ≤ (n + q) ^ k := ha.trans (Nat.pow_le_pow_left (by omega) k)
  rcases Nat.eq_zero_or_pos α with h1 | h1
  · rcases Nat.eq_zero_or_pos i with h2 | h2
    · rcases Nat.eq_zero_or_pos j with h3 | h3
      · subst h1 h2 h3; simp at hrep
      · have : 2 ≤ j * (n + q) ^ k := le_trans hc (Nat.le_mul_of_pos_left _ h3)
        omega
    · have : 2 ≤ i * (n + p) ^ k := le_trans hb (Nat.le_mul_of_pos_left _ h2)
      omega
  · have : 2 ≤ α * n ^ k := le_trans ha (Nat.le_mul_of_pos_left _ h1)
    omega

/-- **Theorem 1.1 for shifted triples.** For `0 < p < q`, `k ≥ 2` and `e = k + ⌈k/2⌉` there are
constants `c, C` such that for every `n ≥ 2` with `gcd(n, p, q) = 1` the Frobenius number `F` of
`⟨n^k, (n+p)^k, (n+q)^k⟩` exists and `n^e ≤ c F`, `F ≤ C n^e`, `n^e ≤ 2 c g`, `g ≤ C n^e`. -/
theorem growthPQ (p q : ℕ) (hp : 0 < p) (hpq : p < q) (k : ℕ) (hk : 2 ≤ k) :
    ∃ c C : ℕ, ∀ n : ℕ, 2 ≤ n → Nat.gcd n (Nat.gcd p q) = 1 →
      ∃ F, FrobeniusNumber F (gensPQ p q k n) ∧
      n ^ (k + (k + 1) / 2) ≤ c * F ∧ F ≤ C * n ^ (k + (k + 1) / 2) ∧
      n ^ (k + (k + 1) / 2) ≤ 2 * c * genus (gensPQ p q k n) ∧
      genus (gensPQ p q k n) ≤ C * n ^ (k + (k + 1) / 2) := by
  obtain ⟨γ, Γ, hγ, hL⟩ := lattice_minima hp hpq k hk
  set d₂ := (k + 1) / 2 with hd₂
  have hd₂1 : 1 ≤ d₂ := by omega
  have hk1 : 1 ≤ k := by omega
  set N₀ := 2 * γ * (2 + (1 + p) ^ k)
  refine ⟨4 * γ + N₀ ^ (k + d₂), 8 * Γ * (1 + q) ^ k, fun n hn hg => ?_⟩
  obtain ⟨-, -, ⟨u, v, hu, hv, huv, hsu, hsv⟩, hsecond⟩ := hL n (by omega) hg
  set a := n ^ k with ha_def
  set b := (n + p) ^ k with hb_def
  set c := (n + q) ^ k with hc_def
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hab : a ≤ b := Nat.pow_le_pow_left (by omega) k
  have hbc : b ≤ c := Nat.pow_le_pow_left (by omega) k
  have hcq : c ≤ (1 + q) ^ k * n ^ k := by
    rw [hc_def, ← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) k
  have hbp : b ≤ (1 + p) ^ k * n ^ k := by
    rw [hb_def, ← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) k
  -- all large integers are representable
  set M := 4 * (Γ * n ^ d₂) * (b + c)
  have hrep : ∀ x, M ≤ x → x ∈ AddSubmonoid.closure (gensPQ p q k n) := by
    intro x hx
    rw [mem_closure_iff]
    exact rep_of_box ha0 (bezout_abc hg) ((inL_iff u).mp hu) ((inL_iff v).mp hv) huv hsu hsv x hx
  obtain ⟨F, hF⟩ := exists_frob_of_rep (one_not_mem hk1 hn) hrep
  have hF1 : 1 ≤ F := hF.2 (one_not_mem hk1 hn)
  -- upper bound
  have hFup : F ≤ 8 * Γ * (1 + q) ^ k * n ^ (k + d₂) := by
    have hFM : F < M := by
      by_contra hcon; push Not at hcon; exact hF.1 (hrep F hcon)
    have h1 : M ≤ 4 * (Γ * n ^ d₂) * (2 * ((1 + q) ^ k * n ^ k)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : 4 * (Γ * n ^ d₂) * (2 * ((1 + q) ^ k * n ^ k)) =
        8 * Γ * (1 + q) ^ k * n ^ (k + d₂) := by rw [pow_add]; ring
    omega
  -- lower bound
  have hFlow : n ^ (k + d₂) ≤ 2 * γ * F + γ * (2 + (1 + p) ^ k) * n ^ k := by
    obtain ⟨u', v', hu', hv', huv', hsu', hsv'⟩ := short_vectors_of_frob ha0 hb0 hbc hF
    have key := hsecond u' v' ((inL_iff u').mpr hu') ((inL_iff v').mpr hv') huv'
    set X := (F + a) / b
    have hX : n ^ d₂ ≤ γ * (2 * X + 1) := key.trans (Nat.mul_le_mul_left _ (max_le hsu' hsv'))
    have hXb : X * b ≤ F + a := Nat.div_mul_le_self _ _
    calc n ^ (k + d₂) = n ^ d₂ * n ^ k := by rw [pow_add]; ring
      _ ≤ (γ * (2 * X + 1)) * b := Nat.mul_le_mul hX hab
      _ = 2 * γ * (X * b) + γ * b := by ring
      _ ≤ 2 * γ * (F + a) + γ * b := by gcongr
      _ = 2 * γ * F + γ * (2 * a + b) := by ring
      _ ≤ 2 * γ * F + γ * (2 + (1 + p) ^ k) * n ^ k := by
          have : 2 * a + b ≤ (2 + (1 + p) ^ k) * n ^ k := by rw [add_mul]; omega
          have := Nat.mul_le_mul_left γ this
          rw [mul_assoc γ (2 + (1 + p) ^ k)]; omega
  have hFlow' : n ^ (k + d₂) ≤ (4 * γ + N₀ ^ (k + d₂)) * F := by
    by_cases hbig : N₀ ≤ n ^ d₂
    · have h1 : N₀ * n ^ k ≤ n ^ (k + d₂) := by
        rw [pow_add, mul_comm (n ^ k)]; exact Nat.mul_le_mul_right _ hbig
      have h2 : n ^ (k + d₂) ≤ 4 * γ * F := by
        have : 2 * (γ * (2 + (1 + p) ^ k) * n ^ k) = N₀ * n ^ k := by simp only [N₀]; ring
        have e : 2 * γ * F = 2 * (γ * F) := by ring
        have h3 : n ^ (k + d₂) ≤ 4 * (γ * F) := by omega
        linarith
      calc n ^ (k + d₂) ≤ 4 * γ * F := h2
        _ ≤ (4 * γ + N₀ ^ (k + d₂)) * F := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    · push Not at hbig
      have hnN : n ≤ N₀ := by
        have : n ≤ n ^ d₂ := by
          calc n = n ^ 1 := (pow_one n).symm
            _ ≤ n ^ d₂ := Nat.pow_le_pow_right (by omega) hd₂1
        omega
      calc n ^ (k + d₂) ≤ N₀ ^ (k + d₂) := Nat.pow_le_pow_left hnN _
        _ ≤ N₀ ^ (k + d₂) * F := Nat.le_mul_of_pos_right _ hF1
        _ ≤ (4 * γ + N₀ ^ (k + d₂)) * F := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  have hg1 := genus_le hF
  have hg2 := frob_succ_le_two_genus hF
  refine ⟨F, hF, hFlow', hFup, ?_, hg1.trans hFup⟩
  calc n ^ (k + d₂) ≤ (4 * γ + N₀ ^ (k + d₂)) * F := hFlow'
    _ ≤ (4 * γ + N₀ ^ (k + d₂)) * (2 * genus (gensPQ p q k n)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (4 * γ + N₀ ^ (k + d₂)) * genus (gensPQ p q k n) := by ring

/-- **Theorem 1.1.** For `k ≥ 2` and `e = k + ⌈k/2⌉` there are constants `c, C` such that for every
`n ≥ 2` the Frobenius number `F` of `S_n^k` exists and satisfies `n^e ≤ c F ≤ c C n^e`, and the
genus satisfies `n^e ≤ 2 c g` and `g ≤ C n^e`. -/
theorem growth (k : ℕ) (hk : 2 ≤ k) :
    ∃ c C : ℕ, ∀ n : ℕ, 2 ≤ n → ∃ F, FrobeniusNumber F (gensK k n) ∧
      n ^ (k + (k + 1) / 2) ≤ c * F ∧ F ≤ C * n ^ (k + (k + 1) / 2) ∧
      n ^ (k + (k + 1) / 2) ≤ 2 * c * genus (gensK k n) ∧
      genus (gensK k n) ≤ C * n ^ (k + (k + 1) / 2) := by
  obtain ⟨c, C, h⟩ := growthPQ 1 2 (by norm_num) (by norm_num) k hk
  exact ⟨c, C, fun n hn => h n hn (by simp)⟩

/-- The generators of `⟨(n+r₁)^k, (n+r₂)^k, (n+r₃)^k⟩` for integer shifts `r₁ < r₂ < r₃`
(only used when `n + r₁ ≥ 2`). -/
abbrev gensR (r₁ r₂ r₃ : ℤ) (k n : ℕ) : Set ℕ :=
  {((n : ℤ) + r₁).toNat ^ k, ((n : ℤ) + r₂).toNat ^ k, ((n : ℤ) + r₃).toNat ^ k}

/-- **Corollary 4.3.** For integers `r₁ < r₂ < r₃` and `k ≥ 2` there are constants `c, C` such that
for every `n ≥ 1` with `n + r₁ ≥ 2` and `gcd(n + r₁, r₂ - r₁, r₃ - r₁) = 1` the Frobenius number `F`
of `⟨(n+r₁)^k, (n+r₂)^k, (n+r₃)^k⟩` exists and `n^e ≤ c F`, `F ≤ C n^e`, `n^e ≤ 2 c g`,
`g ≤ C n^e`. -/
theorem growthR (r₁ r₂ r₃ : ℤ) (h₁₂ : r₁ < r₂) (h₂₃ : r₂ < r₃) (k : ℕ) (hk : 2 ≤ k) :
    ∃ c C : ℕ, ∀ n : ℕ, 1 ≤ n → 2 ≤ (n : ℤ) + r₁ →
      Int.gcd ((n : ℤ) + r₁) (Int.gcd (r₂ - r₁) (r₃ - r₁)) = 1 →
      ∃ F, FrobeniusNumber F (gensR r₁ r₂ r₃ k n) ∧
      n ^ (k + (k + 1) / 2) ≤ c * F ∧ F ≤ C * n ^ (k + (k + 1) / 2) ∧
      n ^ (k + (k + 1) / 2) ≤ 2 * c * genus (gensR r₁ r₂ r₃ k n) ∧
      genus (gensR r₁ r₂ r₃ k n) ≤ C * n ^ (k + (k + 1) / 2) := by
  set p := (r₂ - r₁).toNat with hp_def
  set q := (r₃ - r₁).toNat with hq_def
  have hp : 0 < p := by omega
  have hpq : p < q := by omega
  obtain ⟨c, C, h⟩ := growthPQ p q hp hpq k hk
  set e := k + (k + 1) / 2
  set B := r₁.natAbs + 1
  refine ⟨c * B ^ e, C * B ^ e, fun n hn h2 hg => ?_⟩
  set m := ((n : ℤ) + r₁).toNat with hm_def
  have hm : (m : ℤ) = n + r₁ := by omega
  have hm2 : 2 ≤ m := by omega
  -- the generators
  have e2 : ((n : ℤ) + r₂).toNat = m + p := by omega
  have e3 : ((n : ℤ) + r₃).toNat = m + q := by omega
  have hgens : gensR r₁ r₂ r₃ k n = gensPQ p q k m := by
    simp only [gensR, gensPQ, e2, e3, ← hm_def]
  -- the gcd condition
  have hg' : Nat.gcd m (Nat.gcd p q) = 1 := by
    have h1 : (r₂ - r₁) = (p : ℤ) := by omega
    have h3 : (r₃ - r₁) = (q : ℤ) := by omega
    rw [← hm, h1, h3, Int.gcd_natCast_natCast, Int.gcd_natCast_natCast] at hg
    exact hg
  obtain ⟨F, hF, h1, h2', h3, h4⟩ := h m hm2 hg'
  -- comparison of n and m
  have hnm : n ≤ B * m := by
    have : n ≤ m + r₁.natAbs := by omega
    have : r₁.natAbs ≤ r₁.natAbs * m := Nat.le_mul_of_pos_right _ (by omega)
    simp only [B]; nlinarith
  have hmn : m ≤ B * n := by
    have : m ≤ n + r₁.natAbs := by omega
    have : r₁.natAbs ≤ r₁.natAbs * n := Nat.le_mul_of_pos_right _ hn
    simp only [B]; nlinarith
  have pn : n ^ e ≤ B ^ e * m ^ e := by rw [← mul_pow]; exact Nat.pow_le_pow_left hnm e
  have pm : m ^ e ≤ B ^ e * n ^ e := by rw [← mul_pow]; exact Nat.pow_le_pow_left hmn e
  rw [hgens]
  refine ⟨F, hF, ?_, ?_, ?_, ?_⟩
  · calc n ^ e ≤ B ^ e * m ^ e := pn
      _ ≤ B ^ e * (c * F) := Nat.mul_le_mul_left _ h1
      _ = c * B ^ e * F := by ring
  · calc F ≤ C * m ^ e := h2'
      _ ≤ C * (B ^ e * n ^ e) := Nat.mul_le_mul_left _ pm
      _ = C * B ^ e * n ^ e := by ring
  · calc n ^ e ≤ B ^ e * m ^ e := pn
      _ ≤ B ^ e * (2 * c * genus (gensPQ p q k m)) := Nat.mul_le_mul_left _ h3
      _ = 2 * (c * B ^ e) * genus (gensPQ p q k m) := by ring
  · calc genus (gensPQ p q k m) ≤ C * m ^ e := h4
      _ ≤ C * (B ^ e * n ^ e) := Nat.mul_le_mul_left _ pm
      _ = C * B ^ e * n ^ e := by ring

end GenK
