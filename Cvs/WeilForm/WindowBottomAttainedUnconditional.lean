import Mathlib
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# The bottom of the window's Weil form is attained, unconditionally

    ∃ g ∈ D,  weilForm P R g = inf over D

with no hypothesis beyond `0 ≤ L`: the compactness the direct method needs is `Cvs.WeilForm.ConstraintLimitAdmissible`, and
the semicontinuity is `Cvs.WeilForm.WindowFormLowerSemicontinuous`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowBottomAttainedUnconditional

/-- Every member of the constraint set has a measurable self-convolution. -/
theorem aestronglyMeasurable_selfConvolution {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) :
    AEStronglyMeasurable (selfConvolution f) (volume : Measure ℝ) := by
  have := (Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution
    (Cvs.WeilForm.WindowConstraintSet.integrable_of_mem hL hf)).re
  simpa using this.aestronglyMeasurable

end Cvs.WeilForm.WindowBottomAttainedUnconditional
