import Mathlib
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.WeilPositivityStatement

/-!
# The self-convolution as a cosine integral against its spectral density

    g v = ∫ (‖𝓕 f (t/2π)‖²/2π)·cos(t v) dt,    g = selfConvolution f

Fourier inversion, real parts, and the change of variable to `Cvs.WeilForm.Archimedean.ArchSpectralDensity`'s convention, so the
window form's archimedean term is the symbol against a nonnegative density.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.SelfConvolutionCosine

/-- The spectral density, in `Cvs.WeilForm.Archimedean.ArchSpectralDensity`'s frequency variable. -/
def specDensity (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) (t / (2 * π))‖ ^ 2 / (2 * π)

/-- **It is nonnegative.** -/
theorem specDensity_nonneg (f : ℝ → ℝ) (t : ℝ) : 0 ≤ specDensity f t := by
  unfold specDensity
  positivity

/-- **The self-convolution is a cosine integral against its spectral density.** -/
theorem selfConvolution_eq_cosIntegral {f : ℝ → ℝ} (hfint : Integrable f)
    (hgint : Integrable fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ))
    (hW : Integrable fun ξ : ℝ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2)
    {v : ℝ} (hcont : ContinuousAt (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) v) :
    selfConvolution f v = ∫ t : ℝ, specDensity f t * Real.cos (t * v) := by
  set g : ℝ → ℂ := fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ) with hgdef
  have hFg : 𝓕 g = fun ξ : ℝ =>
      ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 : ℝ) : ℂ) :=
    funext fun ξ => Cvs.WeilForm.SelfConvolutionTransform.fourier_selfConvolution f hfint ξ
  have hFgint : Integrable (𝓕 g) := by rw [hFg]; exact hW.ofReal
  have hinv : 𝓕⁻ (𝓕 g) v = g v := hgint.fourierInv_fourier_eq hFgint hcont
  -- the inversion integral, with the character written out
  have hval : g v = ∫ ξ : ℝ, Complex.exp ((↑(2 * π * ξ * v) : ℂ) * Complex.I)
      * ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hinv, Real.fourierInv_eq_fourier_neg, hFg,
      Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  -- the integrand is integrable, its modulus being the density's
  have hintegrand : Integrable fun ξ : ℝ =>
      Complex.exp ((↑(2 * π * ξ * v) : ℂ) * Complex.I)
        * ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 : ℝ) : ℂ) := by
    have hmeas2 : AEStronglyMeasurable
        (fun ξ : ℝ => ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 : ℝ) : ℂ)) volume := by
      rw [← hFg]; exact hFgint.aestronglyMeasurable
    refine Integrable.mono' hW.norm ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ hmeas2
      exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          ((continuous_const.mul continuous_id).mul continuous_const)).mul
            continuous_const)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [norm_mul, Complex.norm_exp]
      simp
  -- real parts
  have hre : selfConvolution f v
      = ∫ ξ : ℝ, Real.cos (2 * π * ξ * v)
          * ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 := by
    have h1 : (g v).re = selfConvolution f v := by simp [hgdef]
    rw [← h1, hval]
    have hrei := integral_re (𝕜 := ℂ) hintegrand
    rw [show ((∫ ξ : ℝ, Complex.exp ((↑(2 * π * ξ * v) : ℂ) * Complex.I)
        * ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 : ℝ) : ℂ)).re)
      = RCLike.re (∫ ξ : ℝ, Complex.exp ((↑(2 * π * ξ * v) : ℂ) * Complex.I)
        * ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 : ℝ) : ℂ)) from rfl, ← hrei]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show (Complex.exp ((↑(2 * π * ξ * v) : ℂ) * Complex.I)
        * ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 : ℝ) : ℂ)).re
      = Real.cos (2 * π * ξ * v) * ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- the change of variable to `Cvs.WeilForm.Archimedean.ArchSpectralDensity`'s frequency
  rw [hre]
  have hcov := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure ℝ))
    (fun t : ℝ => specDensity f t * Real.cos (t * v)) (2 * π)
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hlhs : (∫ ξ : ℝ, (fun t : ℝ => specDensity f t * Real.cos (t * v)) ((2 * π) • ξ))
      = (∫ ξ : ℝ, Real.cos (2 * π * ξ * v)
          * ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) / (2 * π) := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, specDensity]
    rw [show (2 * π * ξ) / (2 * π) = ξ by field_simp]
    ring
  rw [hlhs] at hcov
  simp only [Module.finrank_self, pow_one, smul_eq_mul] at hcov
  rw [abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)] at hcov
  have hne : (2 * π : ℝ) ≠ 0 := ne_of_gt hpi
  rw [div_eq_inv_mul] at hcov
  exact mul_left_cancel₀ (inv_ne_zero hne) hcov

end Cvs.WeilForm.SelfConvolutionCosine
