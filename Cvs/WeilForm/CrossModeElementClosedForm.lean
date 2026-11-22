import Mathlib

/-!
# The cross-mode element, in closed form

    ∫₀^{1−t} cos(2πmx)·cos(2πn(x+t)) dx
      = (sin 2πnt − sin 2πmt)/(4π(m−n)) − (sin 2πmt + sin 2πnt)/(4π(m+n))

for `m ≠ n`.  With `Cvs.WeilForm.OperatorTestModeClosedForm`'s diagonal this makes the prime side a matrix in closed form.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.WeilForm.CrossModeElementClosedForm

/-- A single oscillation over the window, evaluated. -/
theorem integral_cos_affine {c : ℝ} (hc : c ≠ 0) (d T : ℝ) :
    (∫ x in (0:ℝ)..T, Real.cos (c * x + d))
      = (Real.sin (c * T + d) - Real.sin d) / c := by
  rw [intervalIntegral.integral_comp_mul_add (fun x => Real.cos x) hc d, integral_cos]
  simp only [mul_zero, zero_add, smul_eq_mul]
  field_simp

end Cvs.WeilForm.CrossModeElementClosedForm
