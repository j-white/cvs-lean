import Mathlib
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.NonnegTestPrimeSide
import Cvs.Zeta.ExplicitFormula.TransformContinuityScaling
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# The window transform's square modulus is the spectral density

    ‖windowTransform L f y‖² = 2π · specDensity (indicator (Ioc 0 L) f) y

`Cvs.Zeta.ExplicitFormula.TransformContinuityScaling` writes the truncated test's Fourier transform as the window transform at `2πw`, and
the truncation is the indicator, so the two frequency-side densities are one object.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real
open scoped FourierTransform

namespace Cvs.WeilForm.SpectralDensityModulus

/-- The complexified truncation is the `Detection` truncation. -/
theorem cf_indicator_eq_truncate (L : ℝ) (f : ℝ → ℝ) :
    Cvs.WeilForm.SelfConvolutionTransform.cf (Set.indicator (Set.Ioc 0 L) f)
      = Cvs.Detection.truncate L (fun t => ((f t : ℝ) : ℂ)) := by
  funext s
  rw [Cvs.Detection.truncate_ofReal]
  rfl

/-- **The two frequency-side densities agree.** -/
theorem norm_windowTransform_sq_eq {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) (y : ℝ) :
    ‖Cvs.Detection.windowTransform L (fun t => ((f t : ℝ) : ℂ)) ((y : ℝ) : ℂ)‖ ^ 2
      = 2 * π * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Set.indicator (Set.Ioc 0 L) f) y := by
  have hpi : (2 * π : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  rw [cf_indicator_eq_truncate L f,
    Cvs.Zeta.ExplicitFormula.TransformContinuityScaling.fourier_truncate_eq hL (fun t => ((f t : ℝ) : ℂ)) (y / (2 * π))]
  have hcast : ((2 * π * (y / (2 * π)) : ℝ) : ℂ) = ((y : ℝ) : ℂ) := by
    congr 1
    field_simp
  rw [hcast]
  field_simp

end Cvs.WeilForm.SpectralDensityModulus
