import Mathlib
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityModulus
import Cvs.WeilForm.TruncatedTestContinuous
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# The identification, with the spectral package discharged

    π · weilForm P R (indicator (Ioc 0 L) f) = (analyticSide (sqTransform L f)).re

on `0 < L`, continuity with vanishing endpoints, `CompactTestAdmissibility`'s two window bounds, and the two
index conditions — every spectral hypothesis of `an earlier result` supplied internally.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Complex Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.SpectralIdentification

open Cvs.WeilForm.SelfConvolutionTransform Cvs.WeilForm.Archimedean.ArchimedeanUnbounded Cvs.WeilForm.SelfConvolutionCosine

/-- The truncated test is integrable as a complex-valued function. -/
theorem integrable_truncate {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hfc : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0) :
    Integrable (Cvs.Detection.truncate L (cf f)) := by
  show Integrable (Cvs.Detection.truncate L (fun t : ℝ => ((f t : ℝ) : ℂ)))
  rw [← Cvs.WeilForm.SpectralDensityModulus.cf_indicator_eq_truncate L f]
  exact (Cvs.WeilForm.TruncatedTestContinuous.integrable_indicator hL hfc h0 hLz).ofReal

/-- The spectral density is measurable. -/
theorem measurable_specDensity {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hfc : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0) :
    Measurable (specDensity (Set.indicator (Set.Ioc (0:ℝ) L) f)) := by
  have hFc : Continuous (𝓕 (Cvs.Detection.truncate L (cf f))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_truncate hL hfc h0 hLz)
  unfold specDensity
  rw [Cvs.WeilForm.SpectralDensityModulus.cf_indicator_eq_truncate L f]
  exact ((hFc.comp (continuous_id.div_const (2 * π))).norm.pow 2).measurable.div_const _

end Cvs.WeilForm.SpectralIdentification
