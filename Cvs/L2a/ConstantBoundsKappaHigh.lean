import Mathlib
import Cvs.L2a.ConstantBoundsSbarLambda
import Cvs.L2a.CutRemainderDensity
import Cvs.L2a.RampCutSumsUniform
import Cvs.Upstream.LogFiveSevenBounds
import Cvs.Upstream.LogSquareIntegralTail

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `κ̄_{≥2} ≤ 7.9`

`Φ̄_m` exactly for `2 ≤ m ≤ 10` (`C_m` rational, `log m` enclosed); past `10`, `C_m ≤ 0.2016` gives
`Φ̄_m ≤ 1.0505 log m + 0.0687`, so `σ_mΦ̄_m` is under a log-square majorant and Cvs.Upstream.LogSquareIntegralTail sums the tail.
-/

noncomputable section

open Real Set Cvs.L2a.RampCutSumsUniform Cvs.L2a.CutRemainderDensity Cvs.Upstream.LogSquareIntegralTail Cvs.L2a.ConstantBoundsSbarLambda

namespace Cvs.L2a.ConstantBoundsKappaHigh

theorem phi0_le : phi0 ≤ 603837 / 10000000 := by
  unfold phi0 J1bar eps0
  have h54 : Real.log (5 / 4) = Real.log 5 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  rw [h54, h32]
  linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Cvs.Enclosure.log_five_bounds'.2]

theorem eps3_ge : 3236864 / 100000000 ≤ eps3 := by
  unfold eps3
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  rw [h32]
  linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]

/-- `Φ̄_m` from `log m ≤ L`, `φ₀ ≤ 0.0603837`, `ε₃ ≥ 0.03236864` and the exact `C_m`. -/
theorem PhiBar_le_of {m : ℕ} (hm : 2 ≤ m) {L : ℝ} (hL : Real.log m ≤ L) :
    PhiBar m ≤ L + 603837 / 10000000 + 1 / (m : ℝ) ^ 2
      + CM m * (L / 4 - 3236864 / 100000000 + 1 / (8 * (m : ℝ) ^ 4)) := by
  have hC := CM_nonneg hm
  have := phi0_le
  have := eps3_ge
  unfold PhiBar
  have : CM m * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4))
      ≤ CM m * (L / 4 - 3236864 / 100000000 + 1 / (8 * (m : ℝ) ^ 4)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  linarith

theorem PhiBar_2_le : PhiBar 2 ≤ 13912 / 10000 := by
  have h := PhiBar_le_of (m := 2) (by norm_num) (L := 6931472 / 10000000) (by exact_mod_cast log_small_le.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_3_le : PhiBar 3 ≤ 15412 / 10000 := by
  have h := PhiBar_le_of (m := 3) (by norm_num) (L := 10986123 / 10000000) (by exact_mod_cast log_small_le.2.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_4_le : PhiBar 4 ≤ 17317 / 10000 := by
  have h := PhiBar_le_of (m := 4) (by norm_num) (L := 13862944 / 10000000) (by exact_mod_cast log_small_le.2.2.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_5_le : PhiBar 5 ≤ 19021 / 10000 := by
  have h := PhiBar_le_of (m := 5) (by norm_num) (L := 1609439 / 1000000) (by exact_mod_cast log_small_le.2.2.2.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_6_le : PhiBar 6 ≤ 20507 / 10000 := by
  have h := PhiBar_le_of (m := 6) (by norm_num) (L := 17917595 / 10000000) (by exact_mod_cast log_small_le.2.2.2.2.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_7_le : PhiBar 7 ≤ 21811 / 10000 := by
  have h := PhiBar_le_of (m := 7) (by norm_num) (L := 1945911 / 1000000) (by exact_mod_cast log_small_le.2.2.2.2.2.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_8_le : PhiBar 8 ≤ 22969 / 10000 := by
  have h := PhiBar_le_of (m := 8) (by norm_num) (L := 20794416 / 10000000) (by exact_mod_cast log_small_le.2.2.2.2.2.2.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_9_le : PhiBar 9 ≤ 24008 / 10000 := by
  have h := PhiBar_le_of (m := 9) (by norm_num) (L := 21972246 / 10000000) (by exact_mod_cast log_small_le.2.2.2.2.2.2.2.1)
  unfold CM aU at h
  norm_num at h
  linarith

theorem PhiBar_10_le : PhiBar 10 ≤ 24949 / 10000 := by
  have h := PhiBar_le_of (m := 10) (by norm_num) (L := 23025862 / 10000000) (by exact_mod_cast log_small_le.2.2.2.2.2.2.2.2)
  unfold CM aU at h
  norm_num at h
  linarith

/-- **The `Φ̄` tail**: `Φ̄_m ≤ 1.0505 log m + 0.0687` for `m ≥ 11`. -/
theorem PhiBar_le_tail {m : ℕ} (hm : 11 ≤ m) : PhiBar m ≤ 2101 / 2000 * Real.log m + 687 / 10000 := by
  have hm11 : (11 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : aU m ≤ 121 / 120 := by
    have h3 : aU m ≤ aU 11 := aU_anti (by norm_num) hm11
    have h4 : aU 11 = 121 / 120 := by unfold aU; norm_num
    linarith
  have ha0 : 0 ≤ aU m := by
    unfold aU
    have : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    exact div_nonneg (sq_nonneg _) this.le
  have hC : CM m ≤ 2016 / 10000 := by
    unfold CM
    have h1 : 2 / ((m : ℝ) ^ 2 - 1) ≤ 2 / 120 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    have h2 : 4 * aU m ^ 2 / (2 * m + 1 - aU m) ≤ 4 * (121 / 120) ^ 2 / (23 - 121 / 120) :=
      div_le_div₀ (by positivity) (by gcongr) (by norm_num) (by linarith)
    norm_num at h1 h2 ⊢
    linarith
  have hl : Real.log 11 ≤ Real.log m := Real.log_le_log (by norm_num) hm11
  have hl11 : (2 : ℝ) ≤ Real.log 11 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]; nlinarith [Real.exp_pos 1]
  have he3 := eps3_ge
  have he3' : eps3 ≤ 1 / 10 := by
    unfold eps3
    have : Real.log (3 / 2) ≤ 1 / 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num); linarith
    linarith
  have hB0 : 0 ≤ Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4) := by
    have : 0 ≤ 1 / (8 * (m : ℝ) ^ 4) := by positivity
    linarith
  have hm4 : 1 / (8 * (m : ℝ) ^ 4) ≤ 1 / 117128 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (11 : ℝ) ^ 4 ≤ (m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm11 4
    nlinarith
  have hm2 : 1 / (m : ℝ) ^ 2 ≤ 1 / 121 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hph := phi0_le
  have hX : CM m * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4))
      ≤ 2016 / 10000 * (Real.log m / 4 + 1 / 117128) := by
    calc CM m * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4))
        ≤ 2016 / 10000 * (Real.log m / 4 - eps3 + 1 / (8 * (m : ℝ) ^ 4)) := mul_le_mul_of_nonneg_right hC hB0
      _ ≤ 2016 / 10000 * (Real.log m / 4 + 1 / 117128) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
  unfold PhiBar
  nlinarith

/-- **The head** `Σ_{2 ≤ m ≤ 10} σ_mΦ̄_m ≤ 2.3686`. -/
theorem head_sigma_PhiBar_le :
    ∑ i ∈ Finset.range 11, (if 2 ≤ i then sigma i * PhiBar i else 0) ≤ 23686 / 10000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  have q : ∀ (k : ℕ) (s φ : ℝ), 2 ≤ k → sigma k ≤ s → PhiBar k ≤ φ → sigma k * PhiBar k ≤ s * φ :=
    fun k s φ hk hs hφ => mul_le_mul hs hφ (PhiBar_nonneg hk) (le_trans (sigma_nonneg k) hs)
  have t2 := q 2 _ _ le_rfl sigma_2_le PhiBar_2_le
  have t3 := q 3 _ _ (by norm_num) sigma_3_le PhiBar_3_le
  have t4 := q 4 _ _ (by norm_num) sigma_4_le PhiBar_4_le
  have t5 := q 5 _ _ (by norm_num) sigma_5_le PhiBar_5_le
  have t6 := q 6 _ _ (by norm_num) sigma_6_le PhiBar_6_le
  have t7 := q 7 _ _ (by norm_num) sigma_7_le PhiBar_7_le
  have t8 := q 8 _ _ (by norm_num) sigma_8_le PhiBar_8_le
  have t9 := q 9 _ _ (by norm_num) sigma_9_le PhiBar_9_le
  have t10 := q 10 _ _ (by norm_num) sigma_10_le PhiBar_10_le
  linarith

/-- **`κ̄_{≥2} ≤ 7.9`**. -/
theorem kappaBar2_le : kappaBar2 ≤ 79 / 10 := by
  have hf : ∀ n : ℕ, 0 ≤ (if 2 ≤ n then sigma n * PhiBar n else 0) := fun n => by
    split_ifs with h
    · exact mul_nonneg (sigma_nonneg n) (PhiBar_nonneg h)
    · exact le_rfl
  set a : ℝ := 121 / 120 * (2101 / 2000)
  set b : ℝ := 121 / 120 * (687 / 10000 + 2101 / 2000 * (18 / 25))
  set c : ℝ := 121 / 120 * (18 / 25 * (687 / 10000))
  have ht := tsum_le_head_add_tail hf (M := 10) (by norm_num) (a := a) (b := b) (c := c)
    (by norm_num) (by norm_num) (by norm_num) head_sigma_PhiBar_le fun m hm => by
      rw [if_pos (by omega)]
      have hs := sigma_le_tail (show 11 ≤ m by omega)
      have hφ := PhiBar_le_tail (show 11 ≤ m by omega)
      have hl : 0 ≤ Real.log m := Real.log_natCast_nonneg m
      have hφ0 := PhiBar_nonneg (show 2 ≤ m by omega)
      calc sigma m * PhiBar m ≤ (121 / 120 * (Real.log m + 18 / 25) / (m : ℝ) ^ 2)
            * (2101 / 2000 * Real.log m + 687 / 10000) := mul_le_mul hs hφ hφ0 (by positivity)
        _ = tailf a b c m := by simp only [a, b, c]; unfold tailf; ring
  have hF : tailF a b c 10 ≤ 15411 / 10000 := by
    simp only [a, b, c]
    unfold tailF
    have hl := log_ten_le
    have hl0 := log_ten_ge
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  unfold kappaBar2
  push_cast at ht
  linarith

end Cvs.L2a.ConstantBoundsKappaHigh
