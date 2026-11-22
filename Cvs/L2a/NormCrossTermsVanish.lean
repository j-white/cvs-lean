import Mathlib
import Cvs.Prolate.Envelope.ProlateWeightSizes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The norm's cross terms vanish at window scale `s = c^{2/5}`

With `t = c^{1/10}` (so `c = t¹⁰`, `s = t⁴`, `√s = t²`, `√c = t⁵`): `c · X_m(c, K, c^{2/5}) ≤ C_X(K)/t`,
`C_X = 12√6 a + 5(a + 16) + (π²/3)(80/3) + 96`, `a = √(4K)`, for `c ≥ 1`.
-/

namespace Cvs.L2a.NormCrossTermsVanish

open Real

/-- The constant of the cross terms. -/
noncomputable def Cx (K : ℝ) : ℝ := 12 * √6 * √(4 * K) + 5 * (√(4 * K) + 16) + 2 * (π ^ 2 / 6) * (80 / 3) + 96

theorem rpow_tenth {c : ℝ} (hc : 0 < c) (q : ℕ) : c ^ ((q : ℝ) / 10) = (c ^ ((1 : ℝ) / 10)) ^ q := by
  rw [← rpow_natCast, ← rpow_mul hc.le]; congr 1; ring

/-- **The cross terms at `s = c^{2/5}`**: `c X_m ≤ C_X/c^{1/10}`. -/
theorem c_mul_Xm_le {c K : ℝ} (hc : 1 ≤ c) (hK : 0 ≤ K) :
    c * Cvs.Prolate.Envelope.ProlateWeightSizes.Xm c K (c ^ ((2 : ℝ) / 5)) ≤ Cx K / c ^ ((1 : ℝ) / 10) := by
  have hc0 : 0 < c := by linarith
  set t := c ^ ((1 : ℝ) / 10) with ht
  have ht0 : 0 < t := rpow_pos_of_pos hc0 _
  have ht1 : 1 ≤ t := one_le_rpow hc (by norm_num)
  have hct : c = t ^ 10 := by rw [ht, ← rpow_tenth hc0 10]; norm_num
  have hs : c ^ ((2 : ℝ) / 5) = t ^ 4 := by rw [ht, ← rpow_tenth hc0 4]; norm_num
  have hsc : √c = t ^ 5 := by
    rw [hct, show t ^ 10 = (t ^ 5) ^ 2 by ring, sqrt_sq (by positivity)]
  have hss : √(t ^ 4) = t ^ 2 := by rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, sqrt_sq (by positivity)]
  have hlog : log (t ^ 4) ≤ 4 * t := by
    rw [log_pow]; push_cast
    have := log_le_sub_one_of_pos ht0; linarith
  have hlog0 : 0 ≤ log (t ^ 4) := log_nonneg (one_le_pow₀ ht1)
  set a := √(4 * K) with ha
  have ha0 : 0 ≤ a := sqrt_nonneg _
  unfold Cvs.Prolate.Envelope.ProlateWeightSizes.Xm
  rw [hs, hss, hsc, ← ha]
  rw [hct]
  -- each term times `t¹⁰` is at most a constant over `t`
  have u1 : t ^ 10 * (12 * √6 * a / (t ^ 5 * (t ^ 4 * t ^ 2))) = 12 * √6 * a / t := by field_simp
  have u2 : t ^ 10 * ((a / (t ^ 10 * t ^ 5) + 16 / (t ^ 10 * t ^ 4)) * (1 + log (t ^ 4)))
      ≤ 5 * (a + 16) / t := by
    have e : t ^ 10 * ((a / (t ^ 10 * t ^ 5) + 16 / (t ^ 10 * t ^ 4)) * (1 + log (t ^ 4)))
        = (a / t ^ 5 + 16 / t ^ 4) * (1 + log (t ^ 4)) := by field_simp
    rw [e]
    have hb : a / t ^ 5 + 16 / t ^ 4 ≤ (a + 16) / t ^ 4 := by
      have : a / t ^ 5 ≤ a / t ^ 4 := div_le_div_of_nonneg_left ha0 (by positivity) (by nlinarith [pow_le_pow_right₀ ht1 (show 4 ≤ 5 by norm_num)])
      have e2 : (a + 16) / t ^ 4 = a / t ^ 4 + 16 / t ^ 4 := by ring
      linarith
    calc (a / t ^ 5 + 16 / t ^ 4) * (1 + log (t ^ 4)) ≤ (a + 16) / t ^ 4 * (1 + 4 * t) :=
          mul_le_mul hb (by linarith) (by positivity) (by positivity)
      _ ≤ (a + 16) / t ^ 4 * (5 * t ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 3 by norm_num), pow_le_pow_right₀ ht1 (show 0 ≤ 3 by norm_num)]
      _ = 5 * (a + 16) / t := by field_simp
  have u3 : t ^ 10 * (2 * (16 * t ^ 4 * t ^ 5 / (3 * (t ^ 10) ^ 2) + 16 * t ^ 4 / (t ^ 10) ^ 2
        + 16 * t ^ 4 / (3 * (t ^ 10) ^ 2)) * (π ^ 2 / 6)) ≤ 2 * (π ^ 2 / 6) * (80 / 3) / t := by
    have e : t ^ 10 * (2 * (16 * t ^ 4 * t ^ 5 / (3 * (t ^ 10) ^ 2) + 16 * t ^ 4 / (t ^ 10) ^ 2
        + 16 * t ^ 4 / (3 * (t ^ 10) ^ 2)) * (π ^ 2 / 6))
        = 2 * (π ^ 2 / 6) * (16 / 3 / t + 16 / t ^ 6 + 16 / 3 / t ^ 6) := by field_simp
    rw [e]
    have h6 : 1 / t ^ 6 ≤ 1 / t := one_div_le_one_div_of_le ht0 (by nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 6 by norm_num)])
    have hπ : 0 ≤ 2 * (π ^ 2 / 6) := by positivity
    have : 16 / 3 / t + 16 / t ^ 6 + 16 / 3 / t ^ 6 ≤ 80 / 3 / t := by
      have e1 : 16 / t ^ 6 = 16 * (1 / t ^ 6) := by ring
      have e2 : 16 / 3 / t ^ 6 = 16 / 3 * (1 / t ^ 6) := by ring
      have e3 : 80 / 3 / t = 16 / 3 * (1 / t) + 16 * (1 / t) + 16 / 3 * (1 / t) := by ring
      have e4 : 16 / 3 / t = 16 / 3 * (1 / t) := by ring
      rw [e1, e2, e3, e4]; nlinarith
    calc 2 * (π ^ 2 / 6) * (16 / 3 / t + 16 / t ^ 6 + 16 / 3 / t ^ 6) ≤ 2 * (π ^ 2 / 6) * (80 / 3 / t) :=
          mul_le_mul_of_nonneg_left this hπ
      _ = 2 * (π ^ 2 / 6) * (80 / 3) / t := by ring
  have u4 : t ^ 10 * (96 * t ^ 2 / (t ^ 10) ^ 2) ≤ 96 / t := by
    have e : t ^ 10 * (96 * t ^ 2 / (t ^ 10) ^ 2) = 96 / t ^ 8 := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_left (by norm_num) ht0
    nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 8 by norm_num)]
  have e : Cx K / t = 12 * √6 * a / t + 5 * (a + 16) / t + 2 * (π ^ 2 / 6) * (80 / 3) / t + 96 / t := by
    unfold Cx; rw [← ha]; field_simp
  rw [e, mul_add, mul_add, mul_add]
  linarith

end Cvs.L2a.NormCrossTermsVanish
