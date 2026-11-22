import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.FirstPoleContourShift
import Cvs.Zeta.ExplicitFormula.PoleChannelEvaluated
import Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments

/-!
# The pole channel, against the truncation on the line

    (∫ poleIntegrand + ∫ poleTwo).re = π · 2 · A · M

`PoleChannelEvaluated` gives the channel as `2π·(ofCritical h 1).re`; `Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments` turns that residue into the two
exponential moments of `1_{(0,L]}f` and moves them onto the line.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace Cvs.Zeta.ExplicitFormula.PoleChannelTruncation
open Cvs.Detection

-- The right-hand side is the window form's first term written out: `Detection` precedes
-- `ZeroCounting`, so `Cvs.WeilForm.SelfConvolutionFunctional.weilForm` cannot be named from here.
/-- **The pole channel of a real window test.**  Its real part is `π` times twice the product
of the two exponential moments of the truncation. -/
theorem pole_channel_truncate {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} {ρ : ℝ → ℝ}
    (hd : Differentiable ℂ (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))))
    {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖Cvs.Zeta.ofCritical (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))) z‖
        ≤ A / (1 + |z.im|) ^ 3)
    (hrho : ∀ y : ℝ,
      Cvs.Zeta.ofCritical (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ)))
        (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ)) :
    ((∫ y : ℝ, Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand
          (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))) (2 + (y : ℝ) * I))
        + ∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo
          (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))) (2 + (y : ℝ) * I)).re
      = π * (2 * (∫ s : ℝ, Set.indicator (Set.Ioc 0 L) f s * Real.exp (s / 2))
                 * (∫ s : ℝ, Set.indicator (Set.Ioc 0 L) f s * Real.exp (-(s / 2)))) := by
  rw [Cvs.Detection.pole_channel_eq hd hA hdec hrho,
    Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments.ofCritical_sqTransform_one, Complex.ofReal_re]
  have hpos : (∫ s : ℝ, Set.indicator (Set.Ioc 0 L) f s * Real.exp (s / 2))
      = ∫ s in (0 : ℝ)..L, Real.exp (s / 2) * f s := by
    rw [← Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments.integral_truncate_mul L hL (fun s => Real.exp (s / 2)) f]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  have hneg : (∫ s : ℝ, Set.indicator (Set.Ioc 0 L) f s * Real.exp (-(s / 2)))
      = ∫ s in (0 : ℝ)..L, Real.exp (-s / 2) * f s := by
    rw [← Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments.integral_truncate_mul L hL (fun s => Real.exp (-s / 2)) f]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show Set.indicator (Set.Ioc 0 L) f s * Real.exp (-(s / 2))
      = Real.exp (-s / 2) * Set.indicator (Set.Ioc 0 L) f s
    rw [show (-s / 2 : ℝ) = -(s / 2) by ring]
    ring
  rw [hpos, hneg]
  ring

end Cvs.Zeta.ExplicitFormula.PoleChannelTruncation
