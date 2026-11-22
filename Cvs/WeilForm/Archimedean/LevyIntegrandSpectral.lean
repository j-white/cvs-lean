import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchTrigonometricData
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.ProductIntegrability
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Lévy integrand, resolved over the spectrum

    levy f u = ∫ levyIntegrand t u · specDensity f t dt

so the archimedean energy is a double integral of a nonnegative kernel, and the shift side
and the spectral side are the same quantity read in the two orders.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.Archimedean.LevyIntegrandSpectral

/-- The spectral density of an integrable `L²` function is integrable. -/
theorem integrable_specDensity {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) :
    Integrable (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) (volume : Measure ℝ) :=
  Cvs.WeilForm.ProductIntegrability.integrable_specDensity
    (Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint)

/-- **The Lévy integrand, resolved over the spectrum.** -/
theorem levy_eq_integral {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) (u : ℝ) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u
      = ∫ t : ℝ, Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand t u
          * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := by
  have hgint := Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hfint
  have hFsq := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint
  have hcont : Continuous (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf)
  have hWint := integrable_specDensity hf hfint
  -- the two cosine representations
  have h0 := Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hFsq
    (v := 0) hcont.continuousAt
  have hu := Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hfint hgint hFsq
    (v := u / 2) hcont.continuousAt
  have hcosint : ∀ v : ℝ, Integrable
      (fun t : ℝ => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * Real.cos (t * v))
      (volume : Measure ℝ) := by
    intro v
    refine hWint.mono' ((hWint.aestronglyMeasurable).mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)]
    calc Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * |Real.cos (t * v)|
        ≤ Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
            (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)
      _ = Cvs.WeilForm.SelfConvolutionCosine.specDensity f t := mul_one _
  rw [Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy, h0, hu, ← integral_sub (hcosint 0) (hcosint (u / 2)),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Cvs.WeilForm.Archimedean.ArchTrigonometricData.levyIntegrand, mul_zero, Real.cos_zero, mul_one]
  rw [show t * (u / 2) = t / 2 * u by ring]
  ring

end Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
