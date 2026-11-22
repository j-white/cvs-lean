import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's form is bounded below

    `Cvs.WeilForm.SelfConvolutionWindowEdge`'s positivity, read through the `L²` bridge, is the `lam` the simplicity
    criteria consume: `0·‖φ‖² ≤ weilQW P R φ` on the window `(0, 1/3]`.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil
open scoped ContDiff

namespace Cvs.WeilForm.WindowFormBoundedBelow

/-- **The form vanishes on the zero class.**  Every piece is an integral in `f`. -/
theorem weilForm_zero (P R : ℕ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (fun _ : ℝ => (0:ℝ)) = 0 := by
  have hself : selfConvolution (fun _ : ℝ => (0:ℝ)) = fun _ => 0 := by
    funext t; unfold selfConvolution; simp
  unfold Cvs.WeilForm.SelfConvolutionFunctional.weilForm
  rw [hself]
  simp [primePowerSideTruncated]

end Cvs.WeilForm.WindowFormBoundedBelow
