import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Zeta.ExplicitFormula.AutocorrelationSupport
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# The autocorrelation is a convolution, and its transform is a product
-/

namespace Cvs.Detection

open Complex MeasureTheory FourierTransform Convolution ContinuousLinearMap
open scoped Real

/-- The reflection `g̃(u) = g(−u)`. -/
noncomputable def reflect (g : ℝ → ℂ) : ℝ → ℂ := fun u => g (-u)

theorem integrable_reflect {g : ℝ → ℂ} (hg : Integrable g) : Integrable (reflect g) := by
  show Integrable (fun u : ℝ => g (-u))
  exact hg.comp_neg

/-- **The autocorrelation is a convolution.**  No Fubini is done here; this is
what lets Mathlib's convolution theorem supply it. -/
theorem autocorr_eq_convolution (L : ℝ) (f : ℝ → ℂ) :
    Cvs.Detection.autocorr L f
      = (Cvs.Detection.truncate L f) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (reflect (Cvs.Detection.truncate L f)) := by
  funext v
  rw [Cvs.Detection.autocorr, convolution]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [reflect, ContinuousLinearMap.mul_apply']
  congr 2
  ring

/-- Reflecting a function negates its transform's argument. -/
theorem fourier_reflect (g : ℝ → ℂ) (w : ℝ) : 𝓕 (reflect g) w = 𝓕 g (-w) := by
  show 𝓕 (fun x : ℝ => g (-x)) w = 𝓕 g (-w)
  rw [← Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_neg]

/-- **The autocorrelation's transform is the product.** -/
theorem fourier_autocorr {L : ℝ} {f : ℝ → ℂ} (hf : Continuous f) (w : ℝ) :
    𝓕 (Cvs.Detection.autocorr L f) w
      = 𝓕 (Cvs.Detection.truncate L f) w * 𝓕 (Cvs.Detection.truncate L f) (-w) := by
  have hg : Integrable (Cvs.Detection.truncate L f) := Cvs.Detection.integrable_truncate L hf
  rw [autocorr_eq_convolution,
    Real.fourier_mul_convolution_eq hg (integrable_reflect hg) w, fourier_reflect]

end Cvs.Detection
