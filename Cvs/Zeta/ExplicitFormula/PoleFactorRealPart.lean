import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Cvs.Zeta.ExplicitFormula.VerticalInverseIntegral

/-!
# The real part of the pole factor's vertical integral

`VerticalInverseIntegral` computed `∫_{−R}^{R} dy/(a²+y²)`.
-/

namespace Cvs.Detection

open Complex intervalIntegral MeasureTheory
open scoped Real

/-- An odd function integrates to zero over a symmetric interval. -/
theorem integral_odd_eq_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (R : ℝ) :
    (∫ x in (-R)..R, f x) = 0 := by
  have h1 : (∫ x in (-R)..R, f (-x)) = ∫ x in (-R)..R, f x := by
    rw [intervalIntegral.integral_comp_neg]
    norm_num
  have h2 : (∫ x in (-R)..R, f (-x)) = -∫ x in (-R)..R, f x := by
    simp_rw [hf]
    exact intervalIntegral.integral_neg
  linarith

theorem continuous_inv_line {a : ℝ} (ha : 0 < a) :
    Continuous (fun y : ℝ => (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹) := by
  refine Continuous.inv₀ (by fun_prop) fun y => ?_
  intro hz
  have hre : (((a : ℝ) : ℂ) + (y : ℝ) * I).re = a := by simp
  rw [hz] at hre
  simp at hre
  linarith [hre ▸ ha]

theorem re_inv_line {a : ℝ} (y : ℝ) :
    ((((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).re = a * (a ^ 2 + y ^ 2)⁻¹ := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp
  ring

/-- **The pole factor's vertical integral, in real part.** -/
theorem re_integral_inv_line {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).re = 2 * Real.arctan (R / a) := by
  have hint : IntervalIntegrable (fun y : ℝ => (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)
      volume (-R) R := (continuous_inv_line ha).intervalIntegrable _ _
  have hre : (∫ y in (-R)..R, ((((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).re)
      = (∫ y in (-R)..R, (((a : ℝ) : ℂ) + (y : ℝ) * I)⁻¹).re :=
    intervalIntegral.intervalIntegral_re hint
  rw [← hre]
  simp_rw [re_inv_line]
  rw [intervalIntegral.integral_const_mul, Cvs.Detection.integral_inv_sq_add_sq ha]
  field_simp

end Cvs.Detection
