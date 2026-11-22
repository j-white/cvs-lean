import Mathlib
import Cvs.Prolate.Mellin.RungThreeTermRecurrence

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint asymptotics `s·mel h s → h(1)`

For `h` with derivative `h₁` on `[0, 1]`, bounded by `B₁`, and `Re s > 0`:
`s·mel h s = h(1) − ∫₀¹ w^s h₁(w) dw`, so `|s·mel h s − h(1)| ≤ B₁/(Re s + 1)`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology intervalIntegral

namespace Cvs.Prolate.Mellin.EndpointAsymptotics

open Cvs.Prolate.Mellin.RungThreeTermRecurrence (mel)

variable {h h₁ : ℝ → ℝ}

/-- **Integration by parts at the endpoint**: `s·mel h s + ∫₀¹ w^s h₁(w) dw = h(1)`. -/
theorem mul_mel_add (hd : ∀ w ∈ Icc (0 : ℝ) 1, HasDerivAt h (h₁ w) w) (hc₁ : ContinuousOn h₁ (Icc 0 1))
    {s : ℂ} (hs : 0 < s.re) :
    s * mel h s + ∫ w in (0 : ℝ)..1, (w : ℂ) ^ s * (h₁ w : ℂ) = h 1 := by
  have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
  have hc : ContinuousOn h (Icc 0 1) := fun w hw => (hd w hw).continuousAt.continuousWithinAt
  set f : ℝ → ℂ := fun w => (w : ℂ) ^ s * (h w : ℂ)
  set f' : ℝ → ℂ := fun w => s * (w : ℂ) ^ (s - 1) * (h w : ℂ) + (w : ℂ) ^ s * (h₁ w : ℂ)
  have hfc : ContinuousOn f (Icc 0 1) := by
    refine ContinuousOn.mul ?_ (Complex.continuous_ofReal.comp_continuousOn hc)
    exact (Complex.continuous_ofReal_cpow_const hs).continuousOn
  have hder : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' w) w := by
    intro w hw
    have h1 := hasDerivAt_ofReal_cpow_const hw.1.ne' hs0
    have h2 := (hd w (Ioo_subset_Icc_self hw)).ofReal_comp
    exact (h1.mul h2).congr_deriv (by simp only [f'])
  have hcC : ContinuousOn (fun w => (h w : ℂ)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]; exact Complex.continuous_ofReal.comp_continuousOn hc
  have hc₁C : ContinuousOn (fun w => (h₁ w : ℂ)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]; exact Complex.continuous_ofReal.comp_continuousOn hc₁
  have i1 : IntervalIntegrable (fun w : ℝ => s * (w : ℂ) ^ (s - 1) * (h w : ℂ)) volume 0 1 := by
    have := ((intervalIntegrable_cpow' (r := s - 1) (by simp; linarith)).const_mul s).mul_continuousOn hcC
    simpa [mul_assoc] using this
  have i2 : IntervalIntegrable (fun w : ℝ => (w : ℂ) ^ s * (h₁ w : ℂ)) volume 0 1 :=
    (intervalIntegrable_cpow' (r := s) (by linarith)).mul_continuousOn hc₁C
  have hint : IntervalIntegrable f' volume 0 1 := i1.add i2
  have hftc := integral_eq_sub_of_hasDerivAt_of_le zero_le_one hfc hder hint
  have hf1 : f 1 = h 1 := by simp [f]
  have hf0 : f 0 = 0 := by simp [f, Complex.zero_cpow hs0]
  rw [hf1, hf0, sub_zero] at hftc
  rw [← hftc, intervalIntegral.integral_add i1 i2]
  congr 1
  unfold mel
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun w _ => ?_
  ring

/-- **The endpoint bound**: `|s·mel h s − h(1)| ≤ B₁/(Re s + 1)` if `|h₁| ≤ B₁` on `[0, 1]`. -/
theorem norm_mul_mel_sub_le (hd : ∀ w ∈ Icc (0 : ℝ) 1, HasDerivAt h (h₁ w) w) (hc₁ : ContinuousOn h₁ (Icc 0 1))
    {B₁ : ℝ} (hB : ∀ w ∈ Icc (0 : ℝ) 1, |h₁ w| ≤ B₁) {s : ℂ} (hs : 0 < s.re) :
    ‖s * mel h s - h 1‖ ≤ B₁ / (s.re + 1) := by
  have e := mul_mel_add hd hc₁ hs
  have : s * mel h s - h 1 = -∫ w in (0 : ℝ)..1, (w : ℂ) ^ s * (h₁ w : ℂ) := by
    rw [← e]; ring
  rw [this, norm_neg]
  have hle : ∀ᵐ w ∂volume, w ∈ Ioc (0 : ℝ) 1 → ‖(w : ℂ) ^ s * (h₁ w : ℂ)‖ ≤ B₁ * w ^ s.re := by
    refine Eventually.of_forall fun w hw => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw.1, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB w ⟨hw.1.le, hw.2⟩) (Real.rpow_nonneg hw.1.le _)
  have hii : IntervalIntegrable (fun w : ℝ => B₁ * w ^ s.re) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul B₁
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one hle hii).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), Real.one_rpow,
    Real.zero_rpow (by linarith)]
  ring

end Cvs.Prolate.Mellin.EndpointAsymptotics
