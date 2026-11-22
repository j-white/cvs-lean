import Mathlib
import Cvs.Upstream.FourierMultiplication
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.GaussianRegulariser
import Cvs.WeilForm.RegulariserTransform
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.WeilPositivityStatement

/-!
# The regularised spectral mass is bounded by the energy

    ∫ ‖𝓕 (cf f) ξ‖²·gauss c ξ dξ ≤ ∫ f²

uniformly in `c`, by moving the transform onto the kernel and using that the
self-convolution never exceeds the energy.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.RegularisedSpectralMass

/-- The self-convolution of a window test function is integrable. -/
theorem integrable_selfConvolution {f : ℝ → ℝ}
    (hfint : Integrable f (volume : Measure ℝ)) :
    Integrable (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) (volume : Measure ℝ) := by
  have hcf : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f) (volume : Measure ℝ) := hfint.ofReal
  have hneg : Integrable (fun x : ℝ => Cvs.WeilForm.SelfConvolutionTransform.cf f (-x)) (volume : Measure ℝ) :=
    hcf.comp_neg
  have hconv := hcf.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hneg
  refine hconv.congr (Filter.Eventually.of_forall fun u => ?_)
  exact (Cvs.WeilForm.SelfConvolutionTransform.selfConvolution_eq_convolution f u).symm

/-- **The regularised spectral mass never exceeds the energy.** -/
theorem integral_fourier_sq_gauss_le {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hfint : Integrable f (volume : Measure ℝ)) :
    (∫ ξ : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 * Cvs.WeilForm.GaussianRegulariser.gauss c ξ)
      ≤ ∫ x : ℝ, f x ^ 2 := by
  set E : ℝ := ∫ x : ℝ, f x ^ 2 with hE
  have hselfC := integrable_selfConvolution hfint
  have hselfR : Integrable (selfConvolution f) (volume : Measure ℝ) := by
    have := hselfC.re
    simpa using this
  -- move the transform onto the kernel
  have hmult := Cvs.Upstream.FourierMultiplication.integral_fourier_mul
    (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) (Cvs.WeilForm.RegulariserTransform.gaussC c)
    hselfC (Cvs.WeilForm.RegulariserTransform.integrable_gaussC hc)
  rw [show (fun ξ : ℝ => 𝓕 (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) ξ
      * Cvs.WeilForm.RegulariserTransform.gaussC c ξ)
      = fun ξ : ℝ => ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2
          * Cvs.WeilForm.GaussianRegulariser.gauss c ξ : ℝ) : ℂ) from ?_] at hmult
  · rw [show (fun x : ℝ => ((selfConvolution f x : ℝ) : ℂ) * 𝓕 (Cvs.WeilForm.RegulariserTransform.gaussC c) x)
        = fun x : ℝ => ((selfConvolution f x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x : ℝ) : ℂ)
        from ?_] at hmult
    · rw [integral_complex_ofReal, integral_complex_ofReal] at hmult
      have hreal : (∫ ξ : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2
          * Cvs.WeilForm.GaussianRegulariser.gauss c ξ)
          = ∫ x : ℝ, selfConvolution f x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x :=
        Complex.ofReal_inj.mp hmult
      rw [hreal]
      -- and the kernel side is bounded by the energy
      have hker : Integrable (Cvs.WeilForm.GaussianRegulariser.gaussHat c) (volume : Measure ℝ) := by
        have hpc : (0:ℝ) < π / c := by positivity
        have hg := (integrable_exp_neg_mul_sq hpc).const_mul (Real.sqrt c)⁻¹
        refine hg.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Cvs.WeilForm.GaussianRegulariser.gaussHat]
        congr 2
        ring
      have hprod : Integrable
          (fun x : ℝ => selfConvolution f x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x)
          (volume : Measure ℝ) := by
        refine (hker.const_mul E).mono' (hselfR.aestronglyMeasurable.mul
          hker.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Cvs.WeilForm.GaussianRegulariser.gaussHat_nonneg hc x)]
        exact mul_le_mul_of_nonneg_right
          (Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le x hf)
          (Cvs.WeilForm.GaussianRegulariser.gaussHat_nonneg hc x)
      calc (∫ x : ℝ, selfConvolution f x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x)
          ≤ ∫ x : ℝ, E * Cvs.WeilForm.GaussianRegulariser.gaussHat c x := by
            refine integral_mono hprod (hker.const_mul E) (fun x => ?_)
            refine mul_le_mul_of_nonneg_right ?_
              (Cvs.WeilForm.GaussianRegulariser.gaussHat_nonneg hc x)
            exact le_trans (le_abs_self _)
              (Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le x hf)
        _ = E := by
            rw [integral_const_mul, Cvs.WeilForm.GaussianRegulariser.integral_gaussHat hc, mul_one]
    · funext x
      rw [Cvs.WeilForm.RegulariserTransform.fourier_gaussC hc]
      push_cast
      ring
  · funext ξ
    rw [Cvs.WeilForm.SelfConvolutionTransform.fourier_selfConvolution f hfint ξ, Cvs.WeilForm.RegulariserTransform.gaussC]
    push_cast
    ring

end Cvs.WeilForm.RegularisedSpectralMass
