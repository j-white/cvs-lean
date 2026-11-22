import Mathlib
import Cvs.StepA.EvenPlaneGapByDensity
import Cvs.StepA.StepAFromChannelTruncation
import Cvs.StepA.StepAPredicate
import Cvs.StepA.TruncatedDerivativeFormPrime
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# Step (a) at any scale from three statements about the truncated effective symbol

A trial at level `β`, the odd gap on derivatives above `β`, and the even complement gap above `β`
against the trial, all on the prime side, give Connes–van Suijlekom's step (a) for the window's
Weil form at that scale.
-/

noncomputable section

open MeasureTheory Set

namespace Cvs.StepA.StepAFromEffectiveSymbol

variable {L : ℝ}

/-- **Step (a) from the three symbol statements.** -/
theorem stepA_of_symbol (hL : 0 < L) (P R N : ℕ)
    {w : Cvs.WeilForm.FormDomain.formDomain hL.le} (hw : w ≠ 0)
    {wf : ℝ → ℝ} (hwrep : Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      =ᵐ[volume] wf)
    (hwc : Continuous wf) (hws : ∀ s, s ∉ Ioo (0:ℝ) L → wf s = 0)
    (hwe : ∀ s, wf (L - s) = wf s)
    {β : ℝ} (hβ : Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R w ≤ β * ‖w‖ ^ 2)
    {β' : ℝ} (hββ' : β < β') (hodd : Cvs.StepA.TruncatedDerivativeFormPrime.OddGapDerivTrunc N P R L β')
    {mu2 : ℝ} (hgap : β < mu2)
    (hplane : Cvs.StepA.EvenPlaneGapByDensity.EvenPerpGapTrunc N P R L wf mu2) :
    ∃ η : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.StepA.StepAPredicate.StepA
        (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
          Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) (Cvs.WeilForm.BottomAttained.lam hL P R) η := by
  have hwne : (w : Cvs.WeilForm.WeilFormOnWindowL2.window L) ≠ 0 := fun h => hw (Subtype.ext h)
  exact Cvs.StepA.StepAFromChannelTruncation.stepA_of_trial hL P R N hw hβ
    (Cvs.StepA.TruncatedDerivativeFormPrime.hoddT_of_oddGapDerivTrunc hL N P R hββ' hodd) hgap
    (Cvs.StepA.EvenPlaneGapByDensity.hplane_of_evenPerpGapTrunc hL N P R
      (w : Cvs.WeilForm.WeilFormOnWindowL2.window L) hwrep hwc hws hwe hwne hplane)

end Cvs.StepA.StepAFromEffectiveSymbol
