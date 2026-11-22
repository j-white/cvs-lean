import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# The self-convolution is a convolution, and its transform is a square modulus

    𝓕 (x ↦ f (−x)) = conj (𝓕 f)   for real `f`,   g = f ⋆ f̃,   𝓕 g = ‖𝓕 f‖²

so the spectral density `Cvs.WeilForm.Archimedean.ArchSpectralDensity` integrates against is nonnegative.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform Convolution

namespace Cvs.WeilForm.SelfConvolutionTransform

/-- The test function, complexified. -/
def cf (f : ℝ → ℝ) : ℝ → ℂ := fun x => (f x : ℂ)

/-- **Reflection conjugates the transform**, for a real function. -/
theorem fourier_comp_neg (f : ℝ → ℝ) (w : ℝ) :
    𝓕 (fun x => cf f (-x)) w = starRingEnd ℂ (𝓕 (cf f) w) := by
  have hconj : ∀ y : ℝ,
      starRingEnd ℂ (Complex.exp ((↑(-2 * π * y * w) : ℂ) * Complex.I) • cf f y)
        = Complex.exp ((↑(2 * π * y * w) : ℂ) * Complex.I) • cf f y := by
    intro y
    simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, cf, Complex.conj_ofReal]
    congr 2
    simp only [Complex.conj_I]
    push_cast
    ring
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj, integral_congr_ae (Filter.Eventually.of_forall hconj)]
  have hneg := integral_neg_eq_self
    (fun y : ℝ => Complex.exp ((↑(2 * π * y * w) : ℂ) * Complex.I) • cf f y)
    (volume : Measure ℝ)
  rw [← hneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [cf]
  congr 2
  push_cast
  ring

/-- **The self-convolution is `f` against its reflection.** -/
theorem selfConvolution_eq_convolution (f : ℝ → ℝ) (u : ℝ) :
    ((selfConvolution f u : ℝ) : ℂ)
      = (cf f ⋆[ContinuousLinearMap.mul ℂ ℂ] fun x => cf f (-x)) u := by
  have hshift : (∫ x : ℝ, f x * f (x + u)) = ∫ x : ℝ, f x * f (x - u) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => f x * f (x - u)) u
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x + u - u = x by ring]
    ring
  rw [convolution]
  have hg0 : selfConvolution f u = ∫ x : ℝ, f x * f (x + u) := rfl
  rw [hg0, hshift, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [cf, ContinuousLinearMap.mul_apply']
  push_cast
  rw [show -(u - x) = x - u by ring]

/-- **The spectral density is a square modulus.**  What `Cvs.WeilForm.Archimedean.ArchSpectralDensity`'s `W` is, for the window's
form. -/
theorem fourier_selfConvolution (f : ℝ → ℝ) (hf : Integrable f) (w : ℝ) :
    𝓕 (fun u => ((selfConvolution f u : ℝ) : ℂ)) w
      = (‖𝓕 (cf f) w‖ ^ 2 : ℝ) := by
  have hcf : Integrable (cf f) := by
    unfold cf
    exact hf.ofReal
  have hrefl : Integrable (fun x => cf f (-x)) := hcf.comp_neg
  have hfun : (fun u => ((selfConvolution f u : ℝ) : ℂ))
      = (cf f ⋆[ContinuousLinearMap.mul ℂ ℂ] fun x => cf f (-x)) :=
    funext fun u => selfConvolution_eq_convolution f u
  rw [hfun, Real.fourier_mul_convolution_eq hcf hrefl w, fourier_comp_neg, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

end Cvs.WeilForm.SelfConvolutionTransform
