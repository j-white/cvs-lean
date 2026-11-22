import Mathlib
import Cvs.Upstream.FourierMultiplication
import Cvs.Upstream.GaussianApproximateIdentity
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.GaussianRegulariser
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.RegulariserTransform
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.UnitWindowTransformBounded
import Cvs.Zeta.WeilPositivityStatement

/-!
# Plancherel for a time-limited function

    ∫ ‖𝓕 (cf u) ξ‖² dξ = ∫ u²

The regularised masses agree for every `c`; letting `c → 0` sends one side to the spectral
mass and the other, through the approximate identity, to the self-convolution at the origin.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.Upstream.PlancherelTimeLimited

/-- The kernel side is integrable. -/
theorem integrable_selfConv_mul_gaussHat {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hfint : Integrable f (volume : Measure ℝ)) :
    Integrable (fun x : ℝ => selfConvolution f x * Cvs.WeilForm.GaussianRegulariser.gaussHat c x)
      (volume : Measure ℝ) := by
  have hker : Integrable (Cvs.WeilForm.GaussianRegulariser.gaussHat c) (volume : Measure ℝ) := by
    have hpc : (0:ℝ) < π / c := by positivity
    have hg := (integrable_exp_neg_mul_sq hpc).const_mul (Real.sqrt c)⁻¹
    refine hg.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Cvs.WeilForm.GaussianRegulariser.gaussHat]
    rw [show -π * x ^ 2 / c = -(π / c) * x ^ 2 by ring]
  refine (hker.const_mul (∫ x : ℝ, f x ^ 2)).mono'
    ((Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).aestronglyMeasurable.mul
      hker.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Cvs.WeilForm.GaussianRegulariser.gaussHat_nonneg hc x)]
  exact mul_le_mul_of_nonneg_right
    (Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le x hf)
    (Cvs.WeilForm.GaussianRegulariser.gaussHat_nonneg hc x)

/-- **Plancherel, for a function with compact support.** -/
theorem plancherel_of_integrable {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) :
    (∫ ξ : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) = ∫ x : ℝ, f x ^ 2 := by
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hcdef
  have hcpos : ∀ n, 0 < c n := fun n => by rw [hcdef]; positivity
  have hFint := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint
  -- the spectral side converges to the full mass
  have hA : Tendsto (fun n : ℕ => ∫ ξ : ℝ,
      ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ)
      atTop (nhds (∫ ξ : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2) ?_ ?_ hFint ?_
    · filter_upwards with n
      exact (hFint.aestronglyMeasurable.mul
        (by unfold Cvs.WeilForm.GaussianRegulariser.gauss; fun_prop))
    · filter_upwards with n
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_pos (Cvs.WeilForm.GaussianRegulariser.gauss_pos (c n) ξ)]
      calc ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ
          ≤ ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left
              (Cvs.WeilForm.GaussianRegulariser.gauss_le_one (hcpos n).le ξ) (sq_nonneg _)
        _ = ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2 := mul_one _
    · filter_upwards with ξ
      have hg : Tendsto (fun n : ℕ => Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ) atTop (nhds 1) := by
        have hczero : Tendsto c atTop (nhdsWithin 0 (Set.Ioi 0)) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨by rw [hcdef]; exact tendsto_one_div_add_atTop_nhds_zero_nat,
            Filter.Eventually.of_forall fun n => hcpos n⟩
        exact (Cvs.WeilForm.GaussianRegulariser.tendsto_gauss ξ).comp hczero
      have := hg.const_mul (‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2)
      simpa using this
  -- the kernel side converges to the self-convolution at the origin
  have hB : Tendsto (fun n : ℕ => ∫ x : ℝ,
      selfConvolution f x * Cvs.WeilForm.GaussianRegulariser.gaussHat (c n) x)
      atTop (nhds (selfConvolution f 0)) :=
    Cvs.Upstream.GaussianApproximateIdentity.tendsto_integral_gaussHat
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).measurable
      (fun x => Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le x hf)
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).continuousAt
      (fun c hc => integrable_selfConv_mul_gaussHat hc hf hfint)
  -- and the two sides agree at every `c`
  have heq : ∀ n : ℕ, (∫ ξ : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2
      * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ)
      = ∫ x : ℝ, selfConvolution f x * Cvs.WeilForm.GaussianRegulariser.gaussHat (c n) x := by
    intro n
    have hselfC := Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hfint
    have hmult := Cvs.Upstream.FourierMultiplication.integral_fourier_mul
      (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ))
      (Cvs.WeilForm.RegulariserTransform.gaussC (c n)) hselfC
      (Cvs.WeilForm.RegulariserTransform.integrable_gaussC (hcpos n))
    rw [show (fun ξ : ℝ => 𝓕 (fun u : ℝ => ((selfConvolution f u : ℝ) : ℂ)) ξ
        * Cvs.WeilForm.RegulariserTransform.gaussC (c n) ξ)
        = fun ξ : ℝ => ((‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ^ 2
            * Cvs.WeilForm.GaussianRegulariser.gauss (c n) ξ : ℝ) : ℂ) from ?_] at hmult
    · rw [show (fun x : ℝ => ((selfConvolution f x : ℝ) : ℂ)
          * 𝓕 (Cvs.WeilForm.RegulariserTransform.gaussC (c n)) x)
          = fun x : ℝ => ((selfConvolution f x
              * Cvs.WeilForm.GaussianRegulariser.gaussHat (c n) x : ℝ) : ℂ) from ?_] at hmult
      · rw [integral_complex_ofReal, integral_complex_ofReal] at hmult
        exact Complex.ofReal_inj.mp hmult
      · funext x
        rw [Cvs.WeilForm.RegulariserTransform.fourier_gaussC (hcpos n)]
        push_cast
        ring
    · funext ξ
      rw [Cvs.WeilForm.SelfConvolutionTransform.fourier_selfConvolution f hfint ξ,
        Cvs.WeilForm.RegulariserTransform.gaussC]
      push_cast
      ring
  rw [Cvs.WeilForm.UnitWindowTransformBounded.selfConvolution_zero] at hB
  exact tendsto_nhds_unique (hA.congr heq) hB

end Cvs.Upstream.PlancherelTimeLimited
