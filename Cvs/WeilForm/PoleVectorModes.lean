import Mathlib
import Cvs.WeilForm.PoleFunctionalModeClosedForm

/-!
# The pole vector meets every mode

    ∫_{−L/2}^{L/2} cos(2πn·x/L)·e^{x/2} dx = (−1)ⁿ·sinh(L/4)/(¼ + ωₙ²) ≠ 0

`Cvs.WeilForm.PoleFunctionalModeClosedForm`'s closed form never vanishes, so `Cvs.Finite.NoEigenvalueOnSimpleLevel`'s hypothesis holds at every mode: the rank one
is invisible to no mode at all.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.WeilForm.PoleVectorModes

/-- The pole vector's coefficient at mode `n`, on a window of length `L`. -/
def poleCoeff (L : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (-(L/2))..(L/2), Real.cos (2 * π * n / L * x) * Real.exp (x / 2)

/-- **It never vanishes.**  `Cvs.WeilForm.PoleFunctionalModeClosedForm`'s closed form is a sign times a positive number. -/
theorem poleCoeff_ne_zero {L : ℝ} (hL : 0 < L) (n : ℕ) : poleCoeff L n ≠ 0 := by
  unfold poleCoeff
  rw [Cvs.WeilForm.PoleFunctionalModeClosedForm.pole_functional_mode n hL]
  have hsinh : 0 < Real.sinh (L / 4) := Real.sinh_pos_iff.mpr (by linarith)
  have hden : 0 < 1 / 4 + (2 * π * (n:ℝ) / L) ^ 2 := by positivity
  have hsign : ((-1 : ℝ)) ^ n ≠ 0 := by
    exact pow_ne_zero n (by norm_num)
  refine div_ne_zero ?_ (ne_of_gt hden)
  exact mul_ne_zero hsign (ne_of_gt hsinh)

end Cvs.WeilForm.PoleVectorModes
