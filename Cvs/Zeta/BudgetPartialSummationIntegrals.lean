import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integrals partial summation needs
-/

namespace Cvs.Deficit

open MeasureTheory intervalIntegral

/-- `∫₁ˣ t^{-1/2} dt = 2(√x − 1)`. -/
theorem integral_rpow_neg_half {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc (1:ℝ) x, t ^ (-(1:ℝ)/2) = 2 * (x ^ ((1:ℝ)/2) - 1) := by
  rw [← intervalIntegral.integral_of_le hx, integral_rpow (Or.inl (by norm_num)),
    show (-(1:ℝ)/2 + 1) = (1:ℝ)/2 by ring, Real.one_rpow]
  ring

end Cvs.Deficit
