import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.ConstraintLimitAdmissible
import Cvs.WeilForm.EvennessSurvivesL2Limit
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowBottomAttainedUnconditional
import Cvs.WeilForm.WindowConstraintSet

/-!
# The bottom of the even sector is attained, unconditionally

    ∃ g ∈ Dev,  weilForm P R g = inf over Dev

the even-sector companion to `Cvs.WeilForm.WindowBottomAttainedUnconditional`, with the same compactness supplied by `Cvs.WeilForm.ConstraintLimitAdmissible`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.EvenBottomAttained

/-- The even sector of the window's constraint set. -/
def evenWindowSet (L : ℝ) : Set (ℝ → ℝ) :=
  {f | f ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L
    ∧ (fun x => f (L - x)) =ᵐ[(volume : Measure ℝ)] f}

/-- **The bottom of the even sector is attained.** -/
theorem exists_even_minimiser_window {L lam : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (hlam : IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R '' evenWindowSet L) lam) :
    ∃ g ∈ evenWindowSet L, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g = lam :=
  Cvs.WeilForm.EvennessSurvivesL2Limit.exists_even_minimiser (L := L) P R
    (fun f hf => hf.1) (fun f hf => hf.2.1)
    (fun f hf => Cvs.WeilForm.WindowBottomAttainedUnconditional.aestronglyMeasurable_selfConvolution hL hf)
    (fun f hf => hf.2.2.2) (fun f hf => hf.2.2.1) hlam
    (fun F B hFD hFB => Cvs.WeilForm.ConstraintLimitAdmissible.hcpt hL P R hFD hFB)

end Cvs.WeilForm.EvenBottomAttained
