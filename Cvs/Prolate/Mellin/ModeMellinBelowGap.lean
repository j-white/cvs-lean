import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A prolate mode's Mellin transform below the gap, in closed form

For a solution `(f, u)` of the scaled prolate system of the mode `m` and any solution `(y, v)` of the Euler system
`y' = v/t²`, `v' = −w y`, on `[s, t]` where `D = t²q_m − p_m w > 0`, `c²(m²τ² − 1)² ≥ c² − χ` and `c²m⁴τ⁴ ≥ w`,
`|∫ f y| ≤ 2 (p_m(s) sup|f v| + s² sup|u y|)/D(s)`: `NonresonantCrossIntegral`'s telescoping with the Mellin kernel as partner.
-/

namespace Cvs.Prolate.Mellin.ModeMellinBelowGap

open intervalIntegral Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Mellin.MellinKernelSturmLiouville

/-- **The Mellin cross bound.** -/
theorem euler_cross_le {c χ m w : ℝ} {f u y v : ℝ → ℝ} {s t Mz Mv : ℝ} (hst : s ≤ t) (hm : 0 < m)
    (hs : 1 < m * s) (hD : ∀ τ ∈ Icc s t, 0 < DE c χ m w τ)
    (hA : ∀ τ ∈ Icc s t, c ^ 2 - χ ≤ c ^ 2 * (m ^ 2 * τ ^ 2 - 1) ^ 2)
    (hB : ∀ τ ∈ Icc s t, w ≤ c ^ 2 * m ^ 4 * τ ^ 4)
    (hf : ∀ τ ∈ Icc s t, HasDerivAt f (u τ / pm m τ) τ)
    (hu : ∀ τ ∈ Icc s t, HasDerivAt u (-(qm c χ m τ * f τ)) τ)
    (hy : ∀ τ ∈ Icc s t, HasDerivAt y (v τ / τ ^ 2) τ)
    (hv : ∀ τ ∈ Icc s t, HasDerivAt v (-(w * y τ)) τ)
    (hZ : ∀ τ ∈ Icc s t, |f τ * v τ| ≤ Mz) (hV : ∀ τ ∈ Icc s t, |u τ * y τ| ≤ Mv) :
    |∫ τ in s..t, f τ * y τ| ≤ 2 * (pm m s * Mz + s ^ 2 * Mv) / DE c χ m w s := by
  have hs0 : 0 < s := by
    by_contra h; push Not at h; nlinarith
  have hτ0 : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => lt_of_lt_of_le hs0 hτ.1
  have hpm : ∀ τ ∈ Icc s t, 0 < pm m τ := fun τ hτ => by
    have : 1 < m * τ := lt_of_lt_of_le hs (by nlinarith [hτ.1])
    unfold pm; apply div_pos _ (by positivity); nlinarith
  have hDE : ∀ τ ∈ Icc s t, DE c χ m w τ = τ ^ 2 * qm c χ m τ - pm m τ * w := fun _ _ => rfl
  have hAd : ∀ τ ∈ Icc s t, HasDerivAt (fun τ => 1 * pm m τ / (τ ^ 2 * qm c χ m τ - pm m τ * w))
      ((2 * τ * DE c χ m w τ - pm m τ * dDE c χ m w τ) / DE c χ m w τ ^ 2) τ := fun τ hτ => by
    have := (hasDerivAt_pm hm.ne' τ).div (hasDerivAt_DE (c := c) (χ := χ) (w := w) hm.ne' τ) (hD τ hτ).ne'
    have e : (fun τ => 1 * pm m τ / (τ ^ 2 * qm c χ m τ - pm m τ * w)) = pm m / DE c χ m w := by
      funext τ; simp [DE]
    rw [e]; exact this
  have hBd : ∀ τ ∈ Icc s t, HasDerivAt (fun τ => 1 * τ ^ 2 / (τ ^ 2 * qm c χ m τ - pm m τ * w))
      ((2 * τ * DE c χ m w τ - τ ^ 2 * dDE c χ m w τ) / DE c χ m w τ ^ 2) τ := fun τ hτ => by
    have := (hasDerivAt_pow 2 τ).div (hasDerivAt_DE (c := c) (χ := χ) (w := w) hm.ne' τ) (hD τ hτ).ne'
    have e : (fun τ => 1 * τ ^ 2 / (τ ^ 2 * qm c χ m τ - pm m τ * w)) = (fun τ => τ ^ 2) / DE c χ m w := by
      funext τ; simp [DE]
    rw [e]; refine this.congr_deriv ?_; simp
  have hDc : ContinuousOn (DE c χ m w) (Icc s t) := by unfold DE pm qm; fun_prop
  have hdDc : ContinuousOn (dDE c χ m w) (Icc s t) := by unfold dDE qm; fun_prop
  have hpmc : ContinuousOn (pm m) (Icc s t) := by unfold pm; fun_prop
  have hsq : ∀ τ ∈ Icc s t, DE c χ m w τ ^ 2 ≠ 0 := fun τ hτ => pow_ne_zero 2 (hD τ hτ).ne'
  have key := cross_abs_le (σ := fun _ => 1) (p₂ := fun τ => τ ^ 2) (q₂ := fun _ => w)
    (Mz := Mz) (Mv := Mv) hst
    (fun τ hτ => (hpm τ hτ).ne') (fun τ hτ => by have := hτ0 τ hτ; positivity)
    (fun τ hτ => by rw [← hDE τ hτ]; exact (hD τ hτ).ne')
    hf hu hy (fun τ hτ => by simpa using hv τ hτ) hAd hBd
    (((continuousOn_const.mul continuousOn_id).mul hDc).sub (hpmc.mul hdDc) |>.div (hDc.pow 2) hsq)
    (((continuousOn_const.mul continuousOn_id).mul hDc).sub ((continuousOn_id.pow 2).mul hdDc)
      |>.div (hDc.pow 2) hsq)
    (by
      have h1 : ContinuousOn f (Icc s t) := fun τ hτ => (hf τ hτ).continuousAt.continuousWithinAt
      have h2 : ContinuousOn y (Icc s t) := fun τ hτ => (hy τ hτ).continuousAt.continuousWithinAt
      exact continuousOn_const.mul (h1.mul h2))
    (by unfold qm; fun_prop) continuousOn_const hpmc (continuousOn_id.pow 2)
    (fun τ hτ => by
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      rw [numA_euler hm.ne']
      have := hτ0 τ hτ; have := hA τ hτ
      have : 0 ≤ 2 * τ * (c ^ 2 * (m ^ 2 * τ ^ 2 - 1) ^ 2 - (c ^ 2 - χ)) / m ^ 2 := by
        apply div_nonneg _ (by positivity); apply mul_nonneg (by positivity); linarith
      linarith)
    (fun τ hτ => by
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      rw [numB_euler hm.ne']
      have := hτ0 τ hτ; have := hB τ hτ
      have : 0 ≤ 2 * τ * (c ^ 2 * m ^ 4 * τ ^ 4 - w) / m ^ 2 := by
        apply div_nonneg _ (by positivity); apply mul_nonneg (by positivity); linarith
      linarith)
    (by
      have := hD t (right_mem_Icc.mpr hst); have := hpm t (right_mem_Icc.mpr hst)
      rw [← hDE t (right_mem_Icc.mpr hst)]; positivity)
    (by
      have := hD t (right_mem_Icc.mpr hst)
      rw [← hDE t (right_mem_Icc.mpr hst)]; positivity)
    hZ hV
  simp only [one_mul] at key
  rw [← hDE s (left_mem_Icc.mpr hst)] at key
  calc |∫ τ in s..t, f τ * y τ| ≤ 2 * (pm m s / DE c χ m w s * Mz + s ^ 2 / DE c χ m w s * Mv) := key
    _ = 2 * (pm m s * Mz + s ^ 2 * Mv) / DE c χ m w s := by ring

end Cvs.Prolate.Mellin.ModeMellinBelowGap
