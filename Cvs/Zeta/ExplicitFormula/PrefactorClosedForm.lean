import Mathlib.Analysis.Complex.Exponential

/-!
# The prefactor in closed form
-/

namespace Cvs.Detection

open Real

/-- `e^L = (e^{L/2})²`. -/
theorem exp_half_sq (L : ℝ) : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end Cvs.Detection
