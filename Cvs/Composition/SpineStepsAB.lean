import Mathlib
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.StepA.StepAPredicate
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformNowhereLocallyZero
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# The spine, assembled: step (a) along a sequence of scales and step (b) give RH

The Riemann Hypothesis follows from two statements about the window operator: step (a) at every
scale of a sequence, and step (b), the locally uniform convergence of the scaled minimiser
transforms to `Ξ`. Each transform is entire and, by step (a), zero-free off the axes, which is
what the Hurwitz endpoint consumes.
-/

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Filter Topology

namespace Cvs.Composition.SpineStepsAB

/-- The transform of a scale's normalised minimiser. -/
def transform {L : ℝ} (hL : 0 < L) (η : Cvs.WeilForm.FormDomain.formDomain hL.le) : ℂ → ℂ :=
  FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Limit.ModeSumsToMinimiser.normRep η))

/-- **The transform is entire.** -/
theorem differentiable_transform {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.StepA.StepAPredicate.StepA
      (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
        Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) lam η) :
    Differentiable ℂ (transform hL η) := by
  have hξ := Cvs.Limit.ModeSumsToMinimiser.normRep_mem_evenWindowSet hL.le η h.nonzero h.even
  have hint : Integrable (Cvs.Limit.ModeSumsToMinimiser.normRep η) (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL.le hξ.1.1 hξ.1.2.1
  exact FourierLaplace.differentiable_fourierLaplace_of_integrable hint.ofReal
    (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf hξ.1.2.1)

end Cvs.Composition.SpineStepsAB
