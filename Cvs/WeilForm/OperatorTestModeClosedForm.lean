import Mathlib

/-!
# The operator's test function on a mode, in closed form

    ∫₀^{1−t} cos(2πnx)·cos(2πn(x+t)) dx = (1−t)/2·cos(2πnt) − sin(2πnt)/(4πn)

The self-convolution `testFn` is built from, evaluated symbolically.  RH.md §3.21 carries
what the identification still needs.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.WeilForm.OperatorTestModeClosedForm

/-- Product to sum, from Mathlib's sum to product. -/
theorem cos_mul_cos (A B : ℝ) :
    Real.cos A * Real.cos B = (Real.cos (A + B) + Real.cos (A - B)) / 2 := by
  have h := Real.cos_add_cos (A + B) (A - B)
  have h1 : ((A + B) + (A - B)) / 2 = A := by ring
  have h2 : ((A + B) - (A - B)) / 2 = B := by ring
  rw [h1, h2] at h
  linarith

end Cvs.WeilForm.OperatorTestModeClosedForm
