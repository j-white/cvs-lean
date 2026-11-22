import Mathlib
import Cvs.StepA.StepAFromChannelTruncation
import Cvs.StepA.StepAFromTwoGaps
import Cvs.StepA.StepAPredicate
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# Step (a) assembled at `x = 2`

At `L = log 2`, `P = 2`, `R = 1`, `N = 100`: a nonzero even trial, the odd gap, and the even
plane gap give `StepA` for the Weil form on the form domain of the window of length `log 2`.
-/

noncomputable section

open MeasureTheory Real

namespace Cvs.StepA.StepAAtTwoAssembled

/-- `0 < log 2`. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- **Step (a) at `x = 2`**, from the trial, the odd gap, and the even plane gap. -/
theorem stepA_x2
    {w : Cvs.WeilForm.FormDomain.formDomain log_two_pos.le} (hw : w ≠ 0) {β : ℝ}
    (hβ : Cvs.WeilForm.InfimumAttainedSphere.Q log_two_pos.le 2 1 w ≤ β * ‖w‖ ^ 2)
    (hoddT : ∀ o : Cvs.WeilForm.FormDomain.formDomain log_two_pos.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD log_two_pos.le o = -o → o ≠ 0 →
      β * ‖o‖ ^ 2 < Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1
        (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
    {mu2 : ℝ} (hgap : β < mu2)
    (hplane : ∀ V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain log_two_pos.le),
      Module.finrank ℝ V = 2 → V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub log_two_pos.le →
      ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1
        (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))) :
    ∃ η : Cvs.WeilForm.FormDomain.formDomain log_two_pos.le,
      Cvs.StepA.StepAPredicate.StepA
        (fun v : Cvs.WeilForm.FormDomain.formDomain log_two_pos.le =>
          Cvs.WeilForm.WindowRepresentative.weilQW 2 1 (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD log_two_pos.le)
        (Cvs.WeilForm.BottomAttained.lam log_two_pos 2 1) η :=
  Cvs.StepA.StepAFromChannelTruncation.stepA_of_trial log_two_pos 2 1 100 hw hβ hoddT hgap hplane

end Cvs.StepA.StepAAtTwoAssembled
