import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HaloBound
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments

/-!
# The archimedean channel, evaluated

    (∫ archIntegrand h (2 + yi)).re = ∫ y, archScore y · ρ y

`Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift` shifts the contour to the critical line and `Cvs.Zeta.ExplicitFormula.HaloBound` turns the line integral into a real
pairing; this is the two composed, with the real part taken.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace Cvs.Zeta.ExplicitFormula.ArchimedeanChannelEvaluated
open Cvs.Detection

/-- **The archimedean channel is the score against the density.** -/
theorem arch_channel_line_eq {h : ℂ → ℂ} {ρ : ℝ → ℝ} (hd : Differentiable ℂ h) {A : ℝ}
    (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    (hrho : ∀ y : ℝ, Cvs.Zeta.ofCritical h (1 / 2 + (y : ℝ) * I) = ((ρ y : ℝ) : ℂ))
    (heven : ∀ y : ℝ, ρ (-y) = ρ y) :
    (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand h (2 + (y : ℝ) * I)).re
      = ∫ y : ℝ, Cvs.Detection.archScore y * ρ y := by
  rw [Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.contour_shift hd hA hdec,
    Cvs.Zeta.ExplicitFormula.HaloBound.arch_line_integral_real hd hA hdec hrho heven, Complex.ofReal_re]

/-- **On a real window test**, the density is the modulus squared of the transform, and its
evenness comes for free from `Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments`. -/
theorem arch_channel_window_line {L : ℝ} {f : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hd : Differentiable ℂ (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))))
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖Cvs.Zeta.ofCritical (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))) z‖
        ≤ A / (1 + |z.im|) ^ 3)
    (hrho : ∀ y : ℝ,
      Cvs.Zeta.ofCritical (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ)))
          (1 / 2 + (y : ℝ) * I)
        = ((‖Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) ((y : ℝ))‖ ^ 2 : ℝ) : ℂ)) :
    (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand
        (Cvs.Detection.sqTransform L (fun s => ((f s : ℝ) : ℂ))) (2 + (y : ℝ) * I)).re
      = ∫ y : ℝ, Cvs.Detection.archScore y
          * ‖Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) ((y : ℝ))‖ ^ 2 :=
  arch_channel_line_eq hd hA hdec hrho (fun y => by
    have h := Cvs.Zeta.ExplicitFormula.PoleChannelExpMoments.norm_windowTransform_sq_neg L f y
    rwa [← Complex.ofReal_neg] at h)

end Cvs.Zeta.ExplicitFormula.ArchimedeanChannelEvaluated
