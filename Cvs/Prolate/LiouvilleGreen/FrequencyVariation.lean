import Mathlib
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferRateDerivative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The variation of the frequency

The local frequency `a/p` of a prolate rung is differentiable with derivative `(wqp − 2ξa)/p²` (`PruferRateDerivative`'s `freq'`
with `p' = 2ξ`), which is nonpositive because `χ ≤ c²`, so the frequency decreases and its total variation on `[p, q]`
is exactly `(a/p)(p) − (a/p)(q)`: the frequency's share of `∫|φ''|` in the tests of Cvs.Upstream.FirstDerivativeTestVariation and Cvs.Upstream.SecondDerivativeWindowTest is a closed form
in the two endpoint frequencies, at most `c p/√(p² − 1) − c`.
-/

namespace Cvs.Prolate.LiouvilleGreen.FrequencyVariation

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.PruferRateDerivative

/-- The derivative of `pP`: `2ξ`. -/
theorem hasDerivAt_pP (ξ : ℝ) : HasDerivAt pP (2 * ξ) ξ := by
  have := (hasDerivAt_pow 2 ξ).sub_const 1
  unfold pP
  exact this.congr_deriv (by norm_num)

/-- **The frequency is differentiable** with derivative `freq' pP (2·) (aP) (wP) (qP)`. -/
theorem hasDerivAt_freq {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχc : χ < c ^ 2) :
    HasDerivAt (fun ξ => aP c χ ξ / pP ξ) (freq' pP (fun ξ => 2 * ξ) (aP c χ) (wP c χ) (qP c χ) ξ) ξ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have := (hasDerivAt_aP hξ hc2 hχc).div (hasDerivAt_pP ξ) (pP_pos hξ).ne'
  unfold freq'
  exact this

/-- **The frequency decreases**: `freq' ≤ 0` for `ξ > 1` and `0 ≤ χ < c²`. -/
theorem freq'_nonpos {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (_hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    freq' pP (fun ξ => 2 * ξ) (aP c χ) (wP c χ) (qP c χ) ξ ≤ 0 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp : 0 < pP ξ := pP_pos hξ
  have hq : 0 < qP c χ ξ := qP_pos hξ hc2 hχc
  have ha : 0 < aP c χ ξ := aP_pos hξ hc2 hχc
  have hasq := aP_sq hξ hc2 hχc
  unfold freq'
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  -- `w q p ≤ 2ξ a`, i.e. `dP · p ≤ 4ξ a²`
  have hw : wP c χ ξ * qP c χ ξ = dP c χ ξ / (2 * aP c χ ξ) := by
    unfold wP; field_simp
  rw [hw]
  have hdP : dP c χ ξ * pP ξ ≤ 4 * ξ * aP c χ ξ ^ 2 := by
    rw [hasq]
    unfold dP pP qP
    have : (0 : ℝ) ≤ ξ ^ 2 - 1 := by nlinarith
    have hξ0 : 0 < ξ := by linarith
    nlinarith [mul_nonneg (mul_nonneg hξ0.le this) (sub_nonneg.mpr hχc.le)]
  have : dP c χ ξ / (2 * aP c χ ξ) * pP ξ - aP c χ ξ * (2 * ξ)
      = (dP c χ ξ * pP ξ - 4 * ξ * aP c χ ξ ^ 2) / (2 * aP c χ ξ) := by
    field_simp
    ring
  rw [this]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- **The total variation of the frequency** on `[p, q]` is `(a/p)(p) − (a/p)(q)`. -/
theorem integral_abs_freq' {c χ p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) :
    ∫ ξ in p..q, |freq' pP (fun ξ => 2 * ξ) (aP c χ) (wP c χ) (qP c χ) ξ| = aP c χ p / pP p - aP c χ q / pP q := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hcont : ContinuousOn (fun ξ => freq' pP (fun ξ => 2 * ξ) (aP c χ) (wP c χ) (qP c χ) ξ) (Icc p q) := by
    intro ξ hξ
    have h1 : 1 < ξ := lt_of_lt_of_le hp hξ.1
    unfold freq'
    have hpc : ContinuousAt pP ξ := (hasDerivAt_pP ξ).continuousAt
    have hac : ContinuousAt (aP c χ) ξ := (hasDerivAt_aP h1 hc2 hχc).continuousAt
    have hwc : ContinuousAt (wP c χ) ξ := (hasDerivAt_wP h1 hc2 hχc).continuousAt
    have hqc : ContinuousAt (qP c χ) ξ := by
      unfold qP; fun_prop
    exact (((hwc.mul hqc).mul hpc).sub (hac.mul (continuousAt_id.const_mul 2))).div (hpc.pow 2)
      (pow_ne_zero 2 (pP_pos h1).ne') |>.continuousWithinAt
  have hderiv : ∀ ξ ∈ uIcc p q, HasDerivAt (fun ξ => aP c χ ξ / pP ξ)
      (freq' pP (fun ξ => 2 * ξ) (aP c χ) (wP c χ) (qP c χ) ξ) ξ := by
    intro ξ hξ
    rw [uIcc_of_le hpq] at hξ
    exact hasDerivAt_freq (lt_of_lt_of_le hp hξ.1) hc hχc
  have hneg : ∀ ξ ∈ Icc p q, |freq' pP (fun ξ => 2 * ξ) (aP c χ) (wP c χ) (qP c χ) ξ|
      = -freq' pP (fun ξ => 2 * ξ) (aP c χ) (wP c χ) (qP c χ) ξ := fun ξ hξ =>
    abs_of_nonpos (freq'_nonpos (lt_of_lt_of_le hp hξ.1) hc hχ0 hχc)
  rw [integral_congr (fun ξ hξ => hneg ξ (uIcc_of_le hpq ▸ hξ)), intervalIntegral.integral_neg,
    integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hpq)]
  ring

end Cvs.Prolate.LiouvilleGreen.FrequencyVariation
