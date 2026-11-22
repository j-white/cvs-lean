import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The vertical integral of `1/(a+iy)`, and the residue it computes
-/

namespace Cvs.Detection

open Real intervalIntegral MeasureTheory Filter
open scoped Real Topology

/-- `∫_{−R}^{R} dy/(a²+y²) = (2/a)·arctan(R/a)` for `a > 0`. -/
theorem integral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (∫ y in (-R)..R, (a ^ 2 + y ^ 2)⁻¹) = (2 / a) * Real.arctan (R / a) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hsub : ∀ x : ℝ, (a ^ 2 + (a * x) ^ 2)⁻¹ = a⁻¹ ^ 2 * (1 + x ^ 2)⁻¹ := by
    intro x
    rw [show a ^ 2 + (a * x) ^ 2 = a ^ 2 * (1 + x ^ 2) from by ring, mul_inv]
    congr 1
    rw [← inv_pow]
  have hmul := intervalIntegral.mul_integral_comp_mul_left
    (f := fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) (a := -R / a) (b := R / a) (c := a)
  rw [show a * (-R / a) = -R from by field_simp, show a * (R / a) = R from by field_simp] at hmul
  rw [← hmul]
  simp_rw [hsub]
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_sq,
    show -R / a = -(R / a) from by ring, Real.arctan_neg]
  field_simp
  ring

end Cvs.Detection
