import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.Prolate.LiouvilleGreen.SturmProductByParts
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The telescoping bound when the mode's coefficient increases

`NonresonantCrossIntegral`'s bound with `A = σp₁/D` increasing and `B = σp₂/D` decreasing: `|∫σf₁f₂| ≤ 2(A(t) sup|f₁u₂| + B(s) sup|u₁f₂|)`.
For the Euler partner this holds where `c²(m²τ² − 1)² ≤ c² − χ`, the first mode's strip next to its edge.
-/

namespace Cvs.L2a.TelescopingIncreasingCoeff

open intervalIntegral Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Mellin.MellinKernelSturmLiouville

section generic

variable {f₁ u₁ p₁ q₁ f₂ u₂ p₂ q₂ σ α β : ℝ → ℝ}

/-- **The telescoping bound when `A` increases and `B` decreases.** -/
theorem cross_abs_le_inc {s t Mz Mv : ℝ} (hst : s ≤ t)
    (hp₁ : ∀ r ∈ Icc s t, p₁ r ≠ 0) (hp₂ : ∀ r ∈ Icc s t, p₂ r ≠ 0)
    (hD : ∀ r ∈ Icc s t, p₂ r * q₁ r - p₁ r * q₂ r ≠ 0)
    (hf₁ : ∀ r ∈ Icc s t, HasDerivAt f₁ (u₁ r / p₁ r) r)
    (hu₁ : ∀ r ∈ Icc s t, HasDerivAt u₁ (-(q₁ r * f₁ r)) r)
    (hf₂ : ∀ r ∈ Icc s t, HasDerivAt f₂ (u₂ r / p₂ r) r)
    (hu₂ : ∀ r ∈ Icc s t, HasDerivAt u₂ (-(q₂ r * f₂ r)) r)
    (hA : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (α r) r)
    (hB : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (β r) r)
    (hαc : ContinuousOn α (Icc s t)) (hβc : ContinuousOn β (Icc s t))
    (hc : ContinuousOn (fun r => σ r * (f₁ r * f₂ r)) (Icc s t))
    (hq₁ : ContinuousOn q₁ (Icc s t)) (hq₂ : ContinuousOn q₂ (Icc s t))
    (hpc₁ : ContinuousOn p₁ (Icc s t)) (hpc₂ : ContinuousOn p₂ (Icc s t))
    (hα : ∀ r ∈ Icc s t, 0 ≤ α r) (hβ : ∀ r ∈ Icc s t, β r ≤ 0)
    (hA0 : 0 ≤ σ s * p₁ s / (p₂ s * q₁ s - p₁ s * q₂ s))
    (hB0 : 0 ≤ σ t * p₂ t / (p₂ t * q₁ t - p₁ t * q₂ t))
    (hZ : ∀ r ∈ Icc s t, |f₁ r * u₂ r| ≤ Mz) (hV : ∀ r ∈ Icc s t, |u₁ r * f₂ r| ≤ Mv) :
    |∫ r in s..t, σ r * (f₁ r * f₂ r)|
      ≤ 2 * (σ t * p₁ t / (p₂ t * q₁ t - p₁ t * q₂ t) * Mz
        + σ s * p₂ s / (p₂ s * q₁ s - p₁ s * q₂ s) * Mv) := by
  have hI : uIcc s t = Icc s t := uIcc_of_le hst
  have hmem0 : s ∈ Icc s t := left_mem_Icc.mpr hst
  have hmem1 : t ∈ Icc s t := right_mem_Icc.mpr hst
  have cont : ∀ f : ℝ → ℝ, (∀ r ∈ Icc s t, DifferentiableAt ℝ f r) → ContinuousOn f (Icc s t) :=
    fun f hf r hr => (hf r hr).continuousAt.continuousWithinAt
  have hf₁c := cont f₁ fun r hr => (hf₁ r hr).differentiableAt
  have hu₁c := cont u₁ fun r hr => (hu₁ r hr).differentiableAt
  have hf₂c := cont f₂ fun r hr => (hf₂ r hr).differentiableAt
  have hu₂c := cont u₂ fun r hr => (hu₂ r hr).differentiableAt
  have hid := Cvs.Prolate.LiouvilleGreen.SturmProductByParts.integral_cross hst hp₁ hp₂ hD hf₁ hu₁ hf₂ hu₂ hA hB hαc hβc hc
    hq₁ hq₂ hpc₁ hpc₂
  set A := fun r => σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r)
  set B := fun r => σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r)
  -- A s − A t = −∫ α, and similarly for B
  have hAint : ∫ r in s..t, α r = A t - A s :=
    integral_eq_sub_of_hasDerivAt (fun r hr => hA r (hI ▸ hr)) (hαc.intervalIntegrable_of_Icc hst)
  have hBint : ∫ r in s..t, β r = B t - B s :=
    integral_eq_sub_of_hasDerivAt (fun r hr => hB r (hI ▸ hr)) (hβc.intervalIntegrable_of_Icc hst)
  have iαZ : IntervalIntegrable (fun r => α r * (f₁ r * u₂ r)) MeasureTheory.volume s t :=
    (hαc.mul (hf₁c.mul hu₂c)).intervalIntegrable_of_Icc hst
  have iβV : IntervalIntegrable (fun r => β r * (u₁ r * f₂ r)) MeasureTheory.volume s t :=
    (hβc.mul (hu₁c.mul hf₂c)).intervalIntegrable_of_Icc hst
  have iα : IntervalIntegrable (fun r => α r * Mz) MeasureTheory.volume s t :=
    (hαc.mul continuousOn_const).intervalIntegrable_of_Icc hst
  have iβ : IntervalIntegrable (fun r => -β r * Mv) MeasureTheory.volume s t :=
    ((hβc.neg).mul continuousOn_const).intervalIntegrable_of_Icc hst
  have bαZ : |∫ r in s..t, α r * (f₁ r * u₂ r)| ≤ (A t - A s) * Mz := by
    have h1 : |∫ r in s..t, α r * (f₁ r * u₂ r)| ≤ ∫ r in s..t, |α r * (f₁ r * u₂ r)| :=
      abs_integral_le_integral_abs hst
    have h2 : ∫ r in s..t, |α r * (f₁ r * u₂ r)| ≤ ∫ r in s..t, α r * Mz := by
      apply integral_mono_on hst (iαZ.abs) iα
      intro r hr
      rw [abs_mul, abs_of_nonneg (hα r hr)]
      exact mul_le_mul_of_nonneg_left (hZ r hr) (hα r hr)
    have h3 : ∫ r in s..t, α r * Mz = (A t - A s) * Mz := by
      rw [intervalIntegral.integral_mul_const, hAint]
    linarith
  have bβV : |∫ r in s..t, β r * (u₁ r * f₂ r)| ≤ (B s - B t) * Mv := by
    have h1 : |∫ r in s..t, β r * (u₁ r * f₂ r)| ≤ ∫ r in s..t, |β r * (u₁ r * f₂ r)| :=
      abs_integral_le_integral_abs hst
    have h2 : ∫ r in s..t, |β r * (u₁ r * f₂ r)| ≤ ∫ r in s..t, -β r * Mv := by
      apply integral_mono_on hst (iβV.abs) iβ
      intro r hr
      rw [abs_mul, abs_of_nonpos (hβ r hr)]
      exact mul_le_mul_of_nonneg_left (hV r hr) (by linarith [hβ r hr])
    have h3 : ∫ r in s..t, -β r * Mv = (B s - B t) * Mv := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hBint]; ring
    linarith
  have hAs : A s ≤ A t := by
    have h : 0 ≤ ∫ r in s..t, α r := integral_nonneg hst (fun r hr => hα r hr)
    rw [hAint] at h; linarith
  have hBs : B t ≤ B s := by
    have h : 0 ≤ ∫ r in s..t, -β r := integral_nonneg hst (fun r hr => neg_nonneg.mpr (hβ r hr))
    rw [intervalIntegral.integral_neg, hBint] at h; linarith
  have hA0' : 0 ≤ A s := hA0
  have hB0' : 0 ≤ B t := hB0
  have eZt : |A t * (f₁ t * u₂ t)| ≤ A t * Mz := by
    rw [abs_mul, abs_of_nonneg (hA0'.trans hAs)]; exact mul_le_mul_of_nonneg_left (hZ t hmem1) (hA0'.trans hAs)
  have eVt : |B t * (u₁ t * f₂ t)| ≤ B t * Mv := by
    rw [abs_mul, abs_of_nonneg hB0']; exact mul_le_mul_of_nonneg_left (hV t hmem1) hB0'
  have eZs : |A s * (f₁ s * u₂ s)| ≤ A s * Mz := by
    rw [abs_mul, abs_of_nonneg hA0']
    exact mul_le_mul_of_nonneg_left (hZ s hmem0) hA0'
  have eVs : |B s * (u₁ s * f₂ s)| ≤ B s * Mv := by
    rw [abs_mul, abs_of_nonneg (hB0'.trans hBs)]
    exact mul_le_mul_of_nonneg_left (hV s hmem0) (hB0'.trans hBs)
  have hMz : 0 ≤ Mz := le_trans (abs_nonneg _) (hZ s hmem0)
  have hMv : 0 ≤ Mv := le_trans (abs_nonneg _) (hV s hmem0)
  have hid' : ∫ r in s..t, σ r * (f₁ r * f₂ r)
      = (A t * (f₁ t * u₂ t) - B t * (u₁ t * f₂ t)) - (A s * (f₁ s * u₂ s) - B s * (u₁ s * f₂ s))
        - (∫ r in s..t, α r * (f₁ r * u₂ r)) + ∫ r in s..t, β r * (u₁ r * f₂ r) := hid
  rw [hid', abs_le]
  constructor
  · nlinarith [abs_le.mp eZt, abs_le.mp eVt, abs_le.mp eZs, abs_le.mp eVs, abs_le.mp bαZ, abs_le.mp bβV]
  · nlinarith [abs_le.mp eZt, abs_le.mp eVt, abs_le.mp eZs, abs_le.mp eVs, abs_le.mp bαZ, abs_le.mp bβV]

end generic

/-- **The Mellin cross bound on the edge strip.** -/
theorem euler_cross_le_inc {c χ m w : ℝ} {f u y v : ℝ → ℝ} {s t Mz Mv : ℝ} (hst : s ≤ t) (hm : 0 < m)
    (hs : 1 < m * s) (hD : ∀ τ ∈ Icc s t, 0 < DE c χ m w τ)
    (hA : ∀ τ ∈ Icc s t, c ^ 2 * (m ^ 2 * τ ^ 2 - 1) ^ 2 ≤ c ^ 2 - χ)
    (hB : ∀ τ ∈ Icc s t, w ≤ c ^ 2 * m ^ 4 * τ ^ 4)
    (hf : ∀ τ ∈ Icc s t, HasDerivAt f (u τ / pm m τ) τ)
    (hu : ∀ τ ∈ Icc s t, HasDerivAt u (-(qm c χ m τ * f τ)) τ)
    (hy : ∀ τ ∈ Icc s t, HasDerivAt y (v τ / τ ^ 2) τ)
    (hv : ∀ τ ∈ Icc s t, HasDerivAt v (-(w * y τ)) τ)
    (hZ : ∀ τ ∈ Icc s t, |f τ * v τ| ≤ Mz) (hV : ∀ τ ∈ Icc s t, |u τ * y τ| ≤ Mv) :
    |∫ τ in s..t, f τ * y τ| ≤ 2 * (pm m t / DE c χ m w t * Mz + s ^ 2 / DE c χ m w s * Mv) := by
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
  have key := cross_abs_le_inc (σ := fun _ => 1) (p₂ := fun τ => τ ^ 2) (q₂ := fun _ => w)
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
      apply div_nonneg _ (sq_nonneg _)
      rw [numA_euler hm.ne']
      have := hτ0 τ hτ; have := hA τ hτ
      have : 0 ≤ 2 * τ * ((c ^ 2 - χ) - c ^ 2 * (m ^ 2 * τ ^ 2 - 1) ^ 2) / m ^ 2 := by
        apply div_nonneg _ (by positivity); apply mul_nonneg (by positivity); linarith
      have e : -(2 * τ * (c ^ 2 * (m ^ 2 * τ ^ 2 - 1) ^ 2 - (c ^ 2 - χ)) / m ^ 2)
          = 2 * τ * ((c ^ 2 - χ) - c ^ 2 * (m ^ 2 * τ ^ 2 - 1) ^ 2) / m ^ 2 := by ring
      rw [e]; exact this)
    (fun τ hτ => by
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      rw [numB_euler hm.ne']
      have := hτ0 τ hτ; have := hB τ hτ
      have : 0 ≤ 2 * τ * (c ^ 2 * m ^ 4 * τ ^ 4 - w) / m ^ 2 := by
        apply div_nonneg _ (by positivity); apply mul_nonneg (by positivity); linarith
      linarith)
    (by
      have := hD s (left_mem_Icc.mpr hst); have := hpm s (left_mem_Icc.mpr hst)
      rw [← hDE s (left_mem_Icc.mpr hst)]; positivity)
    (by
      have := hD t (right_mem_Icc.mpr hst)
      rw [← hDE t (right_mem_Icc.mpr hst)]; positivity)
    hZ hV
  simp only [one_mul] at key
  rw [← hDE s (left_mem_Icc.mpr hst), ← hDE t (right_mem_Icc.mpr hst)] at key
  exact key

end Cvs.L2a.TelescopingIncreasingCoeff
