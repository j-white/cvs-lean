import Mathlib
import Cvs.Upstream.PlancherelTimeLimited
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The transform is an isometry on window functions

    ∫ ‖𝓕 (cf f) ξ − 𝓕 (cf h) ξ‖² dξ = ∫ (f x − h x)² dx

`Cvs.Upstream.PlancherelTimeLimited` applied to the difference, the transform being linear on integrable functions.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace Cvs.WeilForm.WindowTransformIsometry

/-- The transform is additive on integrable functions. -/
theorem fourier_sub {f h : ℝ → ℝ} (hfint : Integrable f (volume : Measure ℝ))
    (hhint : Integrable h (volume : Measure ℝ)) (ξ : ℝ) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (f - h)) ξ
      = 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ - 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf h) ξ := by
  have hcf : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f) (volume : Measure ℝ) := hfint.ofReal
  have hch : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf h) (volume : Measure ℝ) := hhint.ofReal
  have hsplit : (Cvs.WeilForm.SelfConvolutionTransform.cf (f - h))
      = Cvs.WeilForm.SelfConvolutionTransform.cf f - Cvs.WeilForm.SelfConvolutionTransform.cf h := by
    funext x
    simp [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.ofReal_sub]
  rw [hsplit, Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_sub]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun v => by simp [smul_sub])
  · exact (Real.fourierIntegral_convergent_iff ξ).mpr hcf
  · exact (Real.fourierIntegral_convergent_iff ξ).mpr hch

/-- **The transform is an isometry.** -/
theorem integral_sub_sq_fourier {f h : ℝ → ℝ}
    (hfh : MemLp (f - h) 2 (volume : Measure ℝ))
    (hfhint : Integrable (f - h) (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ))
    (hhint : Integrable h (volume : Measure ℝ)) :
    (∫ ξ : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ
        - 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf h) ξ‖ ^ 2)
      = ∫ x : ℝ, (f x - h x) ^ 2 := by
  have hP := Cvs.Upstream.PlancherelTimeLimited.plancherel_of_integrable hfh hfhint
  have hpt : (fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ
      - 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf h) ξ‖ ^ 2)
      = fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (f - h)) ξ‖ ^ 2 := by
    funext ξ
    rw [fourier_sub hfint hhint ξ]
  rw [hpt, hP]
  rfl

end Cvs.WeilForm.WindowTransformIsometry
