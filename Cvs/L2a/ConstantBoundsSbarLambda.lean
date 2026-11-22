import Mathlib
import Cvs.L2a.RampCutSumsUniform
import Cvs.Upstream.LogFiveSevenBounds
import Cvs.Upstream.LogSquareIntegralTail
import Cvs.Upstream.WeightedSchurHarmonicSums

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `S̄ ≤ 6.2` and `Λ̄₀ ≤ 14.1`

`σ_m` from rational witnesses `ℓ ≤ √(m² − 1)` for `2 ≤ m ≤ 10`; past `10`, `k_m k_{m+1} ≤ 121/120`, `δ_m ≤ 1/20` and
`H_m − log m ≤ H₁₀ − log 10` give `σ_m ≤ (121/120)(log m + 18/25)/m²`, whose log-square tail is `LogSquareIntegralTail`'s.
-/

noncomputable section

open Real Set Cvs.L2a.RampCutSumsUniform Cvs.Upstream.LogSquareIntegralTail

namespace Cvs.L2a.ConstantBoundsSbarLambda

/-! ### `σ_m` from witnesses -/

/-- `k(u) ≤ u/ℓ` from a witness `ℓ² ≤ u² − 1`. -/
theorem kU_le_of {u ℓ : ℝ} (hu : 1 < u) (hℓ0 : 0 < ℓ) (hℓ : ℓ ^ 2 ≤ u ^ 2 - 1) : kU u ≤ u / ℓ := by
  unfold kU
  exact div_le_div_of_nonneg_left (by linarith) hℓ0 (Real.le_sqrt_of_sq_le hℓ)

/-- **σ from witnesses**: `ℓ² ≤ m² − 1`, `ℓ'² ≤ (m + 1)² − 1`, `δ̂ = m²/ℓ − m < 1`, `π²/6 ≤ Z` give
`σ_m ≤ (m/ℓ)((m + 1)/ℓ')(H_m + Zδ̂/(1 − δ̂))/m²`. -/
theorem sigma_le_of {m : ℕ} (hm : 2 ≤ m) {ℓ ℓ' Z : ℝ} (hℓ0 : 0 < ℓ) (hℓ : ℓ ^ 2 ≤ (m : ℝ) ^ 2 - 1)
    (hℓ'0 : 0 < ℓ') (hℓ' : ℓ' ^ 2 ≤ ((m : ℝ) + 1) ^ 2 - 1) (hδ : (m : ℝ) ^ 2 / ℓ - m < 1)
    (hZ : π ^ 2 / 6 ≤ Z) :
    sigma m ≤ (m / ℓ) * (((m : ℝ) + 1) / ℓ') * (Cvs.Upstream.WeightedSchurHarmonicSums.H m
      + Z * (((m : ℝ) ^ 2 / ℓ - m) / (1 - ((m : ℝ) ^ 2 / ℓ - m)))) / (m : ℝ) ^ 2 := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hk := kU_le_of hm1 hℓ0 hℓ
  have hk1 := kU_le_of (by linarith : (1 : ℝ) < m + 1) hℓ'0 hℓ'
  have hk10 := kU_pos (by linarith : (1 : ℝ) < m + 1)
  have hd0 := delM_pos hm
  have hd2 := delM_le_half hm
  have hdle : delM m ≤ (m : ℝ) ^ 2 / ℓ - m := by
    unfold delM
    have : (m : ℝ) * kU m ≤ (m : ℝ) * (m / ℓ) := mul_le_mul_of_nonneg_left hk (by linarith)
    rw [show (m : ℝ) ^ 2 / ℓ = (m : ℝ) * (m / ℓ) by ring]
    linarith
  have hd' : delM' m ≤ ((m : ℝ) ^ 2 / ℓ - m) / (1 - ((m : ℝ) ^ 2 / ℓ - m)) := by
    unfold delM'
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hd'0 : 0 ≤ delM' m := div_nonneg hd0.le (by linarith)
  have hH := Cvs.Upstream.WeightedSchurHarmonicSums.H_nonneg m
  have hpi : 0 ≤ π ^ 2 / 6 := by positivity
  unfold sigma
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hkk : kU m * kU ((m : ℝ) + 1) ≤ (m / ℓ) * (((m : ℝ) + 1) / ℓ') :=
    mul_le_mul hk hk1 hk10.le (by positivity)
  have hin : Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * delM' m
      ≤ Cvs.Upstream.WeightedSchurHarmonicSums.H m + Z * (((m : ℝ) ^ 2 / ℓ - m) / (1 - ((m : ℝ) ^ 2 / ℓ - m))) := by
    have : π ^ 2 / 6 * delM' m ≤ Z * (((m : ℝ) ^ 2 / ℓ - m) / (1 - ((m : ℝ) ^ 2 / ℓ - m))) :=
      mul_le_mul hZ hd' hd'0 (by linarith)
    linarith
  exact mul_le_mul hkk hin (by positivity) (by positivity)

theorem pi_sq_div_six_le : π ^ 2 / 6 ≤ 16449345 / 10000000 := by
  have h := Real.pi_lt_d6
  have h0 := Real.pi_pos
  nlinarith

theorem H_ten : Cvs.Upstream.WeightedSchurHarmonicSums.H 10 = 7381 / 2520 := by
  unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]

theorem sigma_2_le : sigma 2 ≤ 6850 / 10000 := by
  have h := sigma_le_of (m := 2) (by norm_num) (ℓ := 4330127 / 2500000) (ℓ' := 28284271 / 10000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 2 = 3 / 2 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_3_le : sigma 3 ≤ 2677 / 10000 := by
  have h := sigma_le_of (m := 3) (by norm_num) (ℓ := 28284271 / 10000000) (ℓ' := 38729833 / 10000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 3 = 11 / 6 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_4_le : sigma 4 ≤ 1537 / 10000 := by
  have h := sigma_le_of (m := 4) (by norm_num) (ℓ := 38729833 / 10000000) (ℓ' := 24494897 / 5000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 4 = 25 / 12 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_5_le : sigma 5 ≤ 1024 / 10000 := by
  have h := sigma_le_of (m := 5) (by norm_num) (ℓ := 24494897 / 5000000) (ℓ' := 59160797 / 10000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 5 = 137 / 60 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_6_le : sigma 6 ≤ 741 / 10000 := by
  have h := sigma_le_of (m := 6) (by norm_num) (ℓ := 59160797 / 10000000) (ℓ' := 4330127 / 625000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 6 = 49 / 20 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_7_le : sigma 7 ≤ 5657 / 100000 := by
  have h := sigma_le_of (m := 7) (by norm_num) (ℓ := 4330127 / 625000) (ℓ' := 79372539 / 10000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 7 = 363 / 140 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_8_le : sigma 8 ≤ 4483 / 100000 := by
  have h := sigma_le_of (m := 8) (by norm_num) (ℓ := 79372539 / 10000000) (ℓ' := 89442719 / 10000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 8 = 761 / 280 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_9_le : sigma 9 ≤ 3655 / 100000 := by
  have h := sigma_le_of (m := 9) (by norm_num) (ℓ := 89442719 / 10000000) (ℓ' := 99498743 / 10000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 9 = 7129 / 2520 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

theorem sigma_10_le : sigma 10 ≤ 3045 / 100000 := by
  have h := sigma_le_of (m := 10) (by norm_num) (ℓ := 99498743 / 10000000) (ℓ' := 109544511 / 10000000)
    (Z := 16449345 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pi_sq_div_six_le
  have hH : Cvs.Upstream.WeightedSchurHarmonicSums.H 10 = 7381 / 2520 := by
    unfold Cvs.Upstream.WeightedSchurHarmonicSums.H; norm_num [Finset.sum_range_succ]
  rw [hH] at h
  norm_num at h
  linarith

/-! ### `σ_m` past `10` -/

/-- `H_m ≤ log m + (H₁₀ − log 10)` for `m ≥ 10`: `H_m − log m` decreases. -/
theorem H_le_log_add {m : ℕ} (hm : 10 ≤ m) :
    Cvs.Upstream.WeightedSchurHarmonicSums.H m ≤ Real.log m + (Cvs.Upstream.WeightedSchurHarmonicSums.H 10 - Real.log 10) := by
  have h := Real.strictAnti_eulerMascheroniSeq'.antitone hm
  simp only [Real.eulerMascheroniSeq', show m ≠ 0 by omega, show (10 : ℕ) ≠ 0 by norm_num, if_false] at h
  rw [Cvs.Upstream.WeightedSchurHarmonicSums.H_eq_harmonic, Cvs.Upstream.WeightedSchurHarmonicSums.H_eq_harmonic]
  push_cast at h ⊢
  linarith

/-- `δ_m ≤ 1/20` for `m ≥ 11`. -/
theorem delM_le_twentieth {m : ℕ} (hm : 11 ≤ m) : delM m ≤ 1 / 20 := by
  unfold delM kU
  have hm2 : (11 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < √((m : ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hp
  have hss := Real.sq_sqrt hp.le
  have key : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1 / 20) * √((m : ℝ) ^ 2 - 1) := by
    have h0 : 0 ≤ ((m : ℝ) + 1 / 20) * √((m : ℝ) ^ 2 - 1) := by positivity
    have hsq : ((m : ℝ) ^ 2) ^ 2 ≤ (((m : ℝ) + 1 / 20) * √((m : ℝ) ^ 2 - 1)) ^ 2 := by
      rw [mul_pow, hss]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hm2) (sub_nonneg.2 hm2)) (sub_nonneg.2 hm2)]
    exact le_of_pow_le_pow_left₀ two_ne_zero h0 hsq
  have h2 : (m : ℝ) * ((m : ℝ) / √((m : ℝ) ^ 2 - 1)) ≤ (m : ℝ) + 1 / 20 := by
    rw [mul_div_assoc', div_le_iff₀ hs]; nlinarith [key]
  linarith

theorem log_ten_le : Real.log 10 ≤ 23025862 / 10000000 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_lt_d9, Cvs.Enclosure.log_five_bounds'.2]

theorem log_ten_ge : 23025840 / 10000000 ≤ Real.log 10 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Cvs.Enclosure.log_five_bounds'.1]

/-- **The σ tail**: `σ_m ≤ (121/120)(log m + 18/25)/m²` for `m ≥ 11`. -/
theorem sigma_le_tail {m : ℕ} (hm : 11 ≤ m) :
    sigma m ≤ 121 / 120 * (Real.log m + 18 / 25) / (m : ℝ) ^ 2 := by
  have hm11 : (11 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) < m := by linarith
  have hk0 := kU_pos hm1
  have hk10 := kU_pos (by linarith : (1 : ℝ) < m + 1)
  have hkk : kU m * kU ((m : ℝ) + 1) ≤ 121 / 120 := by
    have h1 : kU ((m : ℝ) + 1) ≤ kU m := kU_anti hm1 (by linarith)
    have h2 : kU m * kU m = aU m := by rw [← sq, kU_sq hm1]
    have h3 : aU m ≤ aU 11 := aU_anti (by norm_num) hm11
    have h4 : aU 11 = 121 / 120 := by unfold aU; norm_num
    nlinarith
  have hd0 := delM_pos (show 2 ≤ m by omega)
  have hd := delM_le_twentieth hm
  have hd' : delM' m ≤ 1 / 19 := by
    unfold delM'; rw [div_le_iff₀ (by linarith)]; linarith
  have hd'0 : 0 ≤ delM' m := div_nonneg hd0.le (by linarith)
  have hH := H_le_log_add (show 10 ≤ m by omega)
  rw [H_ten] at hH
  have hl10 := log_ten_ge
  have hpd : π ^ 2 / 6 * delM' m ≤ 16449345 / 10000000 * (1 / 19) :=
    mul_le_mul pi_sq_div_six_le hd' hd'0 (by norm_num)
  have hin : Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * delM' m ≤ Real.log m + 18 / 25 := by linarith
  have hH0 := Cvs.Upstream.WeightedSchurHarmonicSums.H_nonneg m
  have hin0 : 0 ≤ Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * delM' m := by positivity
  unfold sigma
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc kU m * kU ((m : ℝ) + 1) * (Cvs.Upstream.WeightedSchurHarmonicSums.H m + π ^ 2 / 6 * delM' m)
      ≤ 121 / 120 * (Real.log m + 18 / 25) := mul_le_mul hkk hin hin0 (by norm_num)
    _ = _ := by ring

/-! ### `S̄` and `Λ̄₀` -/

/-- `log m` for `2 ≤ m ≤ 10`, from `log 2`, `log 3`, `log 5`, `log 7`. -/
theorem log_small_le :
    Real.log 2 ≤ 6931472 / 10000000 ∧ Real.log 3 ≤ 10986123 / 10000000 ∧ Real.log 4 ≤ 13862944 / 10000000
    ∧ Real.log 5 ≤ 1609439 / 1000000 ∧ Real.log 6 ≤ 17917595 / 10000000 ∧ Real.log 7 ≤ 1945911 / 1000000
    ∧ Real.log 8 ≤ 20794416 / 10000000 ∧ Real.log 9 ≤ 21972246 / 10000000 ∧ Real.log 10 ≤ 23025862 / 10000000 := by
  have l2 := Real.log_two_lt_d9
  have l3 := Real.log_three_lt_d9
  have l5 := Cvs.Enclosure.log_five_bounds'.2
  have l7 := Cvs.Enclosure.log_seven_bounds'.2
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have e9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    log_ten_le⟩

/-- **The head** `Σ_{m ≤ 10} log m·σ_m ≤ 1.6333`. -/
theorem head_log_sigma_le : ∑ i ∈ Finset.range 11, Real.log i * sigma i ≤ 16333 / 10000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Real.log_zero,
    Real.log_one, zero_mul, zero_add]
  obtain ⟨l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := log_small_le
  have q : ∀ (k : ℕ) (L s : ℝ), Real.log k ≤ L → sigma k ≤ s → Real.log k * sigma k ≤ L * s :=
    fun k L s hL hs => mul_le_mul hL hs (sigma_nonneg k) (le_trans (Real.log_natCast_nonneg k) hL)
  have t2 := q 2 _ _ (by exact_mod_cast l2) sigma_2_le
  have t3 := q 3 _ _ (by exact_mod_cast l3) sigma_3_le
  have t4 := q 4 _ _ (by exact_mod_cast l4) sigma_4_le
  have t5 := q 5 _ _ (by exact_mod_cast l5) sigma_5_le
  have t6 := q 6 _ _ (by exact_mod_cast l6) sigma_6_le
  have t7 := q 7 _ _ (by exact_mod_cast l7) sigma_7_le
  have t8 := q 8 _ _ (by exact_mod_cast l8) sigma_8_le
  have t9 := q 9 _ _ (by exact_mod_cast l9) sigma_9_le
  have t10 := q 10 _ _ (by exact_mod_cast l10) sigma_10_le
  push_cast at t2 t3 t4 t5 t6 t7 t8 t9 t10 ⊢
  linarith

/-- **`S̄ ≤ 6.2`**: the head `m ≤ 10` and the tail of `(121/120)(log²m + (18/25) log m)/m²` from `10`. -/
theorem SBar_le : SBar ≤ 31 / 5 := by
  have hf : ∀ n : ℕ, 0 ≤ Real.log n * sigma n := fun n => mul_nonneg (Real.log_natCast_nonneg n) (sigma_nonneg n)
  have ht := tsum_le_head_add_tail hf (M := 10) (by norm_num) (a := 121 / 120) (b := 121 / 120 * (18 / 25))
    (c := 0) (by norm_num) (by norm_num) le_rfl head_log_sigma_le fun m hm => by
      have hs := sigma_le_tail (show 11 ≤ m by omega)
      have hl : 0 ≤ Real.log m := Real.log_natCast_nonneg m
      calc Real.log m * sigma m ≤ Real.log m * (121 / 120 * (Real.log m + 18 / 25) / (m : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hs hl
        _ = tailf (121 / 120) (121 / 120 * (18 / 25)) 0 m := by unfold tailf; ring
  have hF : tailF (121 / 120) (121 / 120 * (18 / 25)) 0 10 ≤ 14404 / 10000 := by
    unfold tailF
    have hl := log_ten_le
    have hl0 := log_ten_ge
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  unfold SBar
  push_cast at ht
  linarith

theorem phiBar_le : phiBar ≤ 6466211 / 10000000 := by
  unfold phiBar
  have hl : Real.log (3 / 2) ≤ 4054652 / 10000000 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have hp := Real.pi_lt_d6
  have hd : 15 / (4 * 3.141593) + 11 / 16 ≤ 15 / (4 * π) + 11 / 16 := by
    have : 15 / (4 * 3.141593 : ℝ) ≤ 15 / (4 * π) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith [Real.pi_pos]) (by linarith)
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hl0 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  nlinarith

/-- **`Λ̄₀ ≤ 14.1`**. -/
theorem LambdaBar0_le : LambdaBar0 ≤ 141 / 10 := by
  have hS := SBar_le
  have hφ := phiBar_le
  have hφ0 := phiBar_nonneg
  have hp := Real.pi_lt_d6
  have hp0 := Real.pi_pos
  have hpp : 2 * π ^ 2 / 3 - 4 ≤ 2 * 3.141593 ^ 2 / 3 - 4 := by nlinarith
  have hpp0 : 0 ≤ 2 * π ^ 2 / 3 - 4 := by nlinarith [Real.pi_gt_three]
  unfold LambdaBar0
  nlinarith [mul_le_mul hpp hφ hφ0 (by norm_num)]

end Cvs.L2a.ConstantBoundsSbarLambda
