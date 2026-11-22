import Mathlib
import Cvs.L2a.CornerSuprema
import Cvs.L2a.LocalisedConstants

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The joint main term: `r1main + botMain ≤ 0.2925`

The top and bottom main terms of Cvs.L2a.LocalisedConstants bounded jointly in `M`, peaking at `M = 4`: there
`L_far(m, 4) = (2π²m)⁻¹ log((1 + z)/(1 − z))` with the artanh series; `M = 3, 5, 6` explicit;
`M ≥ 7` from `S(M) ≤ 7/(4(M + 1))` and the antitone `R̄₁`, `r̄₁^glob`, `T̄_bot`.
-/
noncomputable section

open Real Finset

namespace Cvs.L2a.JointMainTerm

open Cvs.L2a.CornerSuprema Cvs.L2a.LocalisedConstants

/-- The joint main-term constant `R̄_J = 0.2925`. -/
def RbarJ : ℝ := 2925 / 10000

/-! ### `L_far` through the artanh series -/

/-- `b_m ≤ b̄` from `m⁴ ≤ b̄²(m² − 1)`. -/
theorem bm_le_of {m bU : ℝ} (hm : 1 < m) (hb : 0 ≤ bU) (h : m ^ 4 ≤ bU ^ 2 * (m ^ 2 - 1)) :
    bm m ≤ bU := by
  have hm1 : 0 < m ^ 2 - 1 := by nlinarith
  have hb0 : 0 ≤ bm m := by unfold bm; positivity
  refine le_of_pow_le_pow_left₀ two_ne_zero hb ?_
  rw [bm_sq hm, div_le_iff₀ hm1]; exact h

/-- **The series bound**: with `z = M(b_m − m)/(M² − b_m m) ≤ z̄ < 1`,
`L_far(m, M) ≤ (z̄ + z̄³/3 + z̄⁵/(1 − z̄²))/(π² m)`. -/
theorem Lfar_le_series {m M zU : ℝ} (hm : 2 ≤ m) (hM : m + 1 ≤ M) (hz0 : 0 ≤ zU) (hz1 : zU < 1)
    (hb : bm m * (M + zU * m) ≤ zU * M ^ 2 + M * m) :
    Lfar m M ≤ (zU + zU ^ 3 / 3 + zU ^ 5 / (1 - zU ^ 2)) / m * (π ^ 2)⁻¹ := by
  have hb1 : m < bm m := lt_bm (by linarith)
  have hb3 : bm m - m < 1 / 3 := bm_sub_lt_third hm
  unfold Lfar
  set b := bm m with hbdef
  have hMb : 0 < M - b := by linarith
  have hMm : 0 < M - m := by linarith
  have hD : 0 < M ^ 2 - b * m := by nlinarith
  set z := M * (b - m) / (M ^ 2 - b * m) with hz
  have hz0' : 0 ≤ z := div_nonneg (mul_nonneg (by linarith) (by linarith)) hD.le
  have hzU : z ≤ zU := by rw [hz, div_le_iff₀ hD]; linarith
  have hz1' : z < 1 := lt_of_le_of_lt hzU hz1
  have hA : 0 < (M + b) / (M - b) := by apply div_pos <;> linarith
  have hB : 0 < (M + m) / (M - m) := by apply div_pos <;> linarith
  have e1 : 1 + z = (M + b) * (M - m) / (M ^ 2 - b * m) := by rw [hz]; field_simp; ring
  have e2 : 1 - z = (M - b) * (M + m) / (M ^ 2 - b * m) := by rw [hz]; field_simp; ring
  have hlog : Real.log ((M + b) / (M - b)) - Real.log ((M + m) / (M - m)) =
      Real.log ((1 + z) / (1 - z)) := by
    rw [← Real.log_div hA.ne' hB.ne', e1, e2]
    congr 1
    have : M + m ≠ 0 := by linarith
    field_simp
  have hser := Real.log_div_le_sum_range_add hz0' hz1' 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hser
  norm_num at hser
  have hmono : z + z ^ 3 / 3 + z ^ 5 / (1 - z ^ 2) ≤ zU + zU ^ 3 / 3 + zU ^ 5 / (1 - zU ^ 2) := by
    have h1 : 0 < 1 - zU ^ 2 := by nlinarith
    have a : z ^ 5 / (1 - z ^ 2) ≤ zU ^ 5 / (1 - zU ^ 2) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ hz0' hzU 5) h1 (by nlinarith)
    have c : z ^ 3 ≤ zU ^ 3 := pow_le_pow_left₀ hz0' hzU 3
    linarith
  rw [hlog]
  have hm0 : 0 < m := by linarith
  have hπ : 0 < π ^ 2 := by have := pi_pos; positivity
  rw [show (2 * π ^ 2 * m)⁻¹ * Real.log ((1 + z) / (1 - z)) =
      (2⁻¹ * Real.log ((1 + z) / (1 - z))) / m * (π ^ 2)⁻¹ by field_simp]
  gcongr
  linarith

/-! ### The far sum and `R̄₁` -/

/-- **`S(M) ≤ 7/(4(M + 1))`** for `M ≥ 3`, from the harmonic closed form and `H_n ≤ (n + 1)/2`. -/
theorem farSum_le_seven (M : ℕ) (hM : 3 ≤ M) : farSum M ≤ 7 / (4 * ((M : ℝ) + 1)) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [farSum_eq M (by omega)]
  have hHM : (harmonic M : ℝ) = harmonic (M - 2) + 1 / ((M : ℝ) - 1) + 1 / (M : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega, harmonic_succ, harmonic_succ]; push_cast
    rw [one_div, one_div]; ring_nf
  have hH := harmonic_le_half (M - 2)
  rw [Nat.cast_sub (by omega)] at hH; push_cast at hH
  set H : ℝ := (harmonic (M - 2) : ℝ)
  rw [hHM]
  have e : H / (2 * ((M : ℝ) - 1)) - (H + 1 / ((M : ℝ) - 1) + 1 / M - 3 / 2) / (2 * ((M : ℝ) + 1))
      + H / ((M : ℝ) ^ 2 - 1) =
      (4 * H - 1 - ((M : ℝ) - 1) / M + 3 * ((M : ℝ) - 1) / 2) / (2 * ((M : ℝ) ^ 2 - 1)) := by
    have : (M : ℝ) - 1 ≠ 0 := by linarith
    have : (M : ℝ) + 1 ≠ 0 := by linarith
    have : (M : ℝ) ≠ 0 := by linarith
    have : (M : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by nlinarith) (by linarith)]
  have hx : 0 < (M : ℝ) := by linarith
  have : ((M : ℝ) - 1) / M = 1 - 1 / M := by field_simp
  rw [this]
  have hinv : 1 / (M : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hx (by norm_num)]; linarith
  have hinv0 : 0 ≤ 1 / (M : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hH (by linarith : (0 : ℝ) ≤ M + 1)]

/-- `S(6) = 1/5`. -/
theorem farSum_six : farSum 6 = 1 / 5 := by
  simp [farSum, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]; norm_num

/-- **`R̄₁` is antitone from `M = 4`** under the step at `4`. -/
theorem R1bar_antitone {θ : ℝ} (hstep : √11 / 4 * (5 / 9) * (1 + √(8 / 5)) ≤ Nbar θ 4)
    {M K : ℕ} (hM : 4 ≤ M) (hMK : M ≤ K) : R1bar θ K ≤ R1bar θ M := by
  induction K, hMK using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (R1bar_succ_le hstep n (hM.trans hn)).trans ih

/-- `R̄₁(M) ≤ q` from `N(M) ≤ N` and `s ≤ √(M² − 1)`, with `π > 3.141592`. -/
theorem R1bar_le_of {θ : ℝ} {M : ℕ} {N s q : ℝ} (hN : Nbar θ M ≤ N) (hs : 0 < s)
    (hs2 : s ^ 2 ≤ (M : ℝ) ^ 2 - 1) (hq0 : 0 ≤ q) (hq : N ≤ q * (3141592 / 1000000 * s)) :
    R1bar θ M ≤ q := by
  unfold R1bar
  have hsq : s ≤ √((M : ℝ) ^ 2 - 1) := Real.le_sqrt_of_sq_le hs2
  have hden : 3141592 / 1000000 * s ≤ π * √((M : ℝ) ^ 2 - 1) :=
    mul_le_mul pi_lo.le hsq hs.le pi_pos.le
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
  nlinarith [mul_le_mul_of_nonneg_left hden hq0]

theorem sqrt11_le : √11 ≤ 33166248 / 10000000 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem Nbar_five (θ : ℝ) : Nbar θ 5 = θ / 2 + 7 * √11 / 30 := by
  unfold Nbar; norm_num [harmonic]; ring

theorem Nbar_six (θ : ℝ) : Nbar θ 6 = θ / 2 + 41 * √11 / 140 := by
  unfold Nbar; norm_num [harmonic]; ring

theorem Nbar_seven (θ : ℝ) : Nbar θ 7 = θ / 2 + 761 * √11 / 2240 := by
  unfold Nbar; norm_num [harmonic]; ring

theorem R1bar_three_le : R1bar (Theta 2) 3 ≤ 1135 / 10000 :=
  R1bar_le_of (N := 10079 / 10000) (s := 28284 / 10000)
    (by rw [Nbar_three]; linarith [Theta_two_le]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem R1bar_four_le' : R1bar (Theta 2) 4 ≤ 123725 / 1000000 :=
  R1bar_le_of (N := 10079 / 10000 + 3 * (33166248 / 10000000) / 20) (s := 38729833 / 10000000)
    (by rw [Nbar_four]; linarith [Theta_two_le, sqrt11_le]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem R1bar_five_le : R1bar (Theta 2) 5 ≤ 1158 / 10000 :=
  R1bar_le_of (N := 10079 / 10000 + 7 * (33166248 / 10000000) / 30) (s := 48989 / 10000)
    (by rw [Nbar_five]; linarith [Theta_two_le, sqrt11_le]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem R1bar_six_le : R1bar (Theta 2) 6 ≤ 1065 / 10000 :=
  R1bar_le_of (N := 10079 / 10000 + 41 * (33166248 / 10000000) / 140) (s := 5916 / 1000)
    (by rw [Nbar_six]; linarith [Theta_two_le, sqrt11_le]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem R1bar_seven_le : R1bar (Theta 2) 7 ≤ 981 / 10000 :=
  R1bar_le_of (N := 10079 / 10000 + 761 * (33166248 / 10000000) / 2240) (s := 6928 / 1000)
    (by rw [Nbar_seven]; linarith [Theta_two_le, sqrt11_le]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! ### The bottom sums -/

theorem inv_pi_sq_le : (π ^ 2)⁻¹ ≤ 1 / (3141592 / 1000000) ^ 2 := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by positivity) (pi_pow_bounds 2 (by norm_num)).1.le

theorem Lnear_le' {m : ℝ} (hm : 2 < m) : Lnear m ≤ 3 / 4 * nearTerm m * (π ^ 2)⁻¹ := by
  have := Lnear_le hm
  have e : 3 / (4 * π ^ 2) * nearTerm m = 3 / 4 * nearTerm m * (π ^ 2)⁻¹ := by
    have : π ^ 2 ≠ 0 := by have := pi_pos; positivity
    field_simp
  linarith

/-- **The bottom sum through `S(M)`**: for `K ≤ M`,
`Σ_{2 ≤ m < K} (L_near(m) + L_far(m, M)) ≤ 17/1000 + (3/4 · 7/200 + 5/8 · S(M))/π²`. -/
theorem bot_le_farSum (M K : ℕ) (hK : K ≤ M) :
    ∑ m ∈ Ico 2 K, (Lnear m + Lfar m M) ≤
      17 / 1000 + (3 / 4 * (7 / 200) + 5 / 8 * farSum M) * (π ^ 2)⁻¹ := by
  have hπ : 0 < π ^ 2 := by have := pi_pos; positivity
  rw [Finset.sum_add_distrib]
  have hfar : ∑ m ∈ Ico 2 K, Lfar m M ≤ 5 / (8 * π ^ 2) * farSum M := by
    refine le_trans ?_ (sum_Lfar_le_farSum M)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hK)
    intro m hm _
    simp only [mem_Ico] at hm
    exact Lfar_nonneg (by exact_mod_cast hm.1) (by exact_mod_cast hm.2)
  have hnear : ∑ m ∈ Ico 2 K, Lnear m ≤ Lnear 2 + 3 / (4 * π ^ 2) * nearTail := by
    rcases Nat.lt_or_ge 2 K with h | h
    · rw [Finset.sum_eq_sum_Ico_succ_bot h]
      push_cast
      gcongr
      calc ∑ m ∈ Ico 3 K, Lnear m ≤ ∑ m ∈ Ico 3 K, 3 / (4 * π ^ 2) * nearTerm m := by
            apply Finset.sum_le_sum; intro m hm; simp only [mem_Ico] at hm
            have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
            exact Lnear_le (by linarith)
        _ ≤ 3 / (4 * π ^ 2) * nearTail := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_Ico_nearTerm_le_nearTail K) (by positivity)
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      have := Lnear_nonneg (le_refl (2 : ℝ))
      have := nearTail_nonneg
      positivity
  have hL := Lnear_two_bounds.2
  have hT : 3 / (4 * π ^ 2) * nearTail ≤ 3 / (4 * π ^ 2) * (7 / 200) :=
    mul_le_mul_of_nonneg_left nearTail_le (by positivity)
  have e : 3 / (4 * π ^ 2) * (7 / 200) + 5 / (8 * π ^ 2) * farSum M =
      (3 / 4 * (7 / 200) + 5 / 8 * farSum M) * (π ^ 2)⁻¹ := by
    field_simp
  linarith

/-- `√s ≤ S` from `s ≤ c₀ + A/π²` and `c₀ + A/3.141592² ≤ S²`. -/
theorem sqrt_le_of {s c₀ A S : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (h : s ≤ c₀ + A * (π ^ 2)⁻¹)
    (hn : c₀ + A * (1 / (3141592 / 1000000) ^ 2) ≤ S ^ 2) : √s ≤ S := by
  rw [Real.sqrt_le_left hS]
  have := mul_le_mul_of_nonneg_left inv_pi_sq_le hA
  linarith

/-- `b₃ ≤ 3.1819806`, `b₄ ≤ 4.1311823`. -/
theorem bm_three_le : bm 3 ≤ 31819806 / 10000000 :=
  bm_le_of (by norm_num) (by norm_num) (by norm_num)

theorem bm_four_le : bm 4 ≤ 41311823 / 10000000 :=
  bm_le_of (by norm_num) (by norm_num) (by norm_num)

/-- The bottom sum through a bound `S(M) ≤ F`. -/
theorem bot_le_of_farSum {M K : ℕ} (hK : K ≤ M) {F : ℝ} (hF : farSum M ≤ F) :
    ∑ m ∈ Ico 2 K, (Lnear m + Lfar m M) ≤ 17 / 1000 + (3 / 4 * (7 / 200) + 5 / 8 * F) * (π ^ 2)⁻¹ := by
  have h := bot_le_farSum M K hK
  have hp : 0 ≤ (π ^ 2)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hF hp]

theorem bot_three_le :
    √(∑ m ∈ Ico (2 : ℕ) 3, (Lnear (m : ℝ) + Lfar (m : ℝ) ((3 : ℕ) : ℝ))) ≤ 1671 / 10000 := by
  have hs : ∑ m ∈ Ico (2 : ℕ) 3, (Lnear (m : ℝ) + Lfar (m : ℝ) ((3 : ℕ) : ℝ)) = Lnear 2 + Lfar 2 3 := by
    rw [Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty]; norm_num
  have f23 := Lfar_le_series (m := 2) (M := 3) (zU := 2118607 / 10000000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [bm_two_bounds.2])
  have hL := Lnear_two_bounds.2
  have g : (2118607 / 10000000 + (2118607 / 10000000 : ℝ) ^ 3 / 3 +
      (2118607 / 10000000) ^ 5 / (1 - (2118607 / 10000000) ^ 2)) / 2 ≤ 10773869 / 50000000 / 2 := by
    norm_num
  have hp : 0 ≤ (π ^ 2)⁻¹ := by positivity
  refine sqrt_le_of (A := 10773869 / 50000000 / 2) (c₀ := 17 / 1000) (S := 1671 / 10000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  rw [hs]
  nlinarith [mul_le_mul_of_nonneg_right g hp]

theorem bot_four_le :
    √(∑ m ∈ Ico (2 : ℕ) 4, (Lnear (m : ℝ) + Lfar (m : ℝ) ((4 : ℕ) : ℝ))) ≤ 1687 / 10000 := by
  have hs : ∑ m ∈ Ico (2 : ℕ) 4, (Lnear (m : ℝ) + Lfar (m : ℝ) ((4 : ℕ) : ℝ)) =
      Lnear 2 + Lfar 2 4 + (Lnear 3 + Lfar 3 4) := by
    rw [Finset.sum_Ico_succ_top (by norm_num), Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self,
      Finset.sum_empty]; norm_num
  have f24 := Lfar_le_series (m := 2) (M := 4) (zU := 271853 / 2500000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [bm_two_bounds.2])
  have f34 := Lfar_le_series (m := 3) (M := 4) (zU := 1127853 / 10000000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [bm_three_le])
  have n3 := Lnear_le' (m := 3) (by norm_num)
  have hn3 : nearTerm 3 = 61 / 2205 := by norm_num [nearTerm]
  rw [hn3] at n3
  have hL := Lnear_two_bounds.2
  have g1 : (271853 / 2500000 + (271853 / 2500000 : ℝ) ^ 3 / 3 +
      (271853 / 2500000) ^ 5 / (1 - (271853 / 2500000) ^ 2)) / 2 ≤ 272963 / 2500000 / 2 := by
    norm_num
  have g2 : (1127853 / 10000000 + (1127853 / 10000000 : ℝ) ^ 3 / 3 +
      (1127853 / 10000000) ^ 5 / (1 - (1127853 / 10000000) ^ 2)) / 3 ≤ 5664101 / 50000000 / 3 := by
    norm_num
  have hp : 0 ≤ (π ^ 2)⁻¹ := by positivity
  refine sqrt_le_of (A := 3 / 4 * (61 / 2205) + 272963 / 2500000 / 2 + 5664101 / 50000000 / 3)
    (c₀ := 17 / 1000) (S := 1687 / 10000) (by norm_num) (by norm_num) ?_ (by norm_num)
  rw [hs]
  nlinarith [mul_le_mul_of_nonneg_right g1 hp, mul_le_mul_of_nonneg_right g2 hp]

theorem bot_five_le :
    √(∑ m ∈ Ico (2 : ℕ) 5, (Lnear (m : ℝ) + Lfar (m : ℝ) ((5 : ℕ) : ℝ))) ≤ 1658 / 10000 := by
  have hs : ∑ m ∈ Ico (2 : ℕ) 5, (Lnear (m : ℝ) + Lfar (m : ℝ) ((5 : ℕ) : ℝ)) =
      Lnear 2 + Lfar 2 5 + (Lnear 3 + Lfar 3 5) + (Lnear 4 + Lfar 4 5) := by
    rw [Finset.sum_Ico_succ_top (by norm_num), Finset.sum_Ico_succ_top (by norm_num),
      Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty]; norm_num
  have f25 := Lfar_le_series (m := 2) (M := 5) (zU := 189759 / 2500000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [bm_two_bounds.2])
  have f35 := Lfar_le_series (m := 3) (M := 5) (zU := 29439 / 500000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [bm_three_le])
  have f45 := Lfar_le_series (m := 4) (M := 5) (zU := 773913 / 10000000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith [bm_four_le])
  have n3 := Lnear_le' (m := 3) (by norm_num)
  have n4 := Lnear_le' (m := 4) (by norm_num)
  have hn3 : nearTerm 3 = 61 / 2205 := by norm_num [nearTerm]
  have hn4 : nearTerm 4 = 83 / 18816 := by norm_num [nearTerm]
  rw [hn3] at n3
  rw [hn4] at n4
  have hL := Lnear_two_bounds.2
  have g1 : (189759 / 2500000 + (189759 / 2500000 : ℝ) ^ 3 / 3 +
      (189759 / 2500000) ^ 5 / (1 - (189759 / 2500000) ^ 2)) / 2 ≤ 7605191 / 100000000 / 2 := by
    norm_num
  have g2 : (29439 / 500000 + (29439 / 500000 : ℝ) ^ 3 / 3 +
      (29439 / 500000) ^ 5 / (1 - (29439 / 500000) ^ 2)) / 3 ≤ 235787 / 4000000 / 3 := by
    norm_num
  have g3 : (773913 / 10000000 + (773913 / 10000000 : ℝ) ^ 3 / 3 +
      (773913 / 10000000) ^ 5 / (1 - (773913 / 10000000) ^ 2)) / 4 ≤ 7754861 / 100000000 / 4 := by
    norm_num
  have hp : 0 ≤ (π ^ 2)⁻¹ := by positivity
  refine sqrt_le_of (A := 3 / 4 * (61 / 2205 + 83 / 18816) + 7605191 / 100000000 / 2 +
    235787 / 4000000 / 3 + 7754861 / 100000000 / 4)
    (c₀ := 17 / 1000) (S := 1658 / 10000) (by norm_num) (by norm_num) ?_ (by norm_num)
  rw [hs]
  nlinarith [mul_le_mul_of_nonneg_right g1 hp, mul_le_mul_of_nonneg_right g2 hp,
    mul_le_mul_of_nonneg_right g3 hp]

/-- **The joint main-term bound**: for `κ ≤ 1` and every `M ≥ 3`, `r1main + botMain ≤ 0.2925`. -/
theorem main_le_RbarJ {κ : ℝ} (hκ1 : κ ≤ 1) {M : ℕ} (hM : 3 ≤ M) :
    Cvs.L2a.LocalisedConstants.r1main κ M + Cvs.L2a.LocalisedConstants.botMain κ M ≤ RbarJ := by
  have hθ0 : 0 ≤ Theta 2 := by linarith [Theta_two_ge]
  have hstep := step_of_ge Theta_two_ge
  unfold r1main botMain RbarJ
  rcases Nat.lt_or_ge M 68 with h68 | h68
  · rw [if_pos h68, min_eq_left (by omega), if_neg (by omega), add_zero]
    rcases Nat.lt_or_ge M 7 with h7 | h7
    · interval_cases M
      · linarith [R1bar_three_le, bot_three_le]
      · linarith [R1bar_four_le', bot_four_le]
      · linarith [R1bar_five_le, bot_five_le]
      · have hb := sqrt_le_of (A := 3 / 4 * (7 / 200) + 5 / 8 * (1 / 5)) (c₀ := 17 / 1000)
          (S := 1798 / 10000) (by norm_num) (by norm_num)
          (bot_le_of_farSum (M := 6) le_rfl farSum_six.le) (by norm_num)
        linarith [R1bar_six_le]
    · have ht := (R1bar_antitone hstep (by norm_num : 4 ≤ 7) h7).trans R1bar_seven_le
      have hF : farSum M ≤ 7 / 32 := by
        refine (farSum_le_seven M hM).trans ?_
        have : (7 : ℝ) ≤ M := by exact_mod_cast h7
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hb := sqrt_le_of (A := 3 / 4 * (7 / 200) + 5 / 8 * (7 / 32)) (c₀ := 17 / 1000)
        (S := 1831 / 10000) (by norm_num) (by norm_num) (bot_le_of_farSum le_rfl hF) (by norm_num)
      linarith
  · rw [if_neg (by omega)]
    have hF : farSum M ≤ 7 / 276 := by
      refine (farSum_le_seven M hM).trans ?_
      have : (68 : ℝ) ≤ M := by exact_mod_cast h68
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hb := sqrt_le_of (A := 3 / 4 * (7 / 200) + 5 / 8 * (7 / 276)) (c₀ := 17 / 1000)
      (S := 1459 / 10000) (by norm_num) (by norm_num)
      (bot_le_of_farSum (min_le_left M 550) hF) (by norm_num)
    split_ifs with h550
    · have a := r1glob_antitone (κ := κ) hstep (by norm_num : 4 ≤ 551) (show 551 ≤ M by omega)
      have b := r1globBar_le_one hκ1 hθ0 (M := 551) (by norm_num)
      have c := Tbar_le_one hκ1 (m := 550) (by norm_num)
      have d := Tbar_r1glob_550_le
      linarith
    · have a := r1glob_antitone (κ := κ) hstep (by norm_num : 4 ≤ 68) h68
      have b := r1globBar_le_one hκ1 hθ0 (M := 68) (by norm_num)
      have d := r1globBar_68_le
      linarith

end Cvs.L2a.JointMainTerm

end
