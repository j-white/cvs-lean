import Mathlib
import Cvs.Upstream.PlancherelConvergenceTransfer
import Cvs.WeilForm.EvennessSurvivesL2Limit
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.WindowTransformIsometry

/-!
# The two families are isometric

    dist (toLp f) (toLp h) = dist (toLp (𝓕 (cf f))) (toLp (𝓕 (cf h)))

`Cvs.WeilForm.WindowTransformIsometry` in the language of `Lp` classes, which is what `Cvs.Upstream.TotallyBoundedDistPreserving` consumes.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace Cvs.WeilForm.TransformFamiliesIsometric

/-- The transform of a window function is in `L²`. -/
theorem memLp_fourier {f : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) :
    MemLp (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f)) 2 (volume : Measure ℝ) := by
  have hFc : Continuous (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      hfint.ofReal
  rw [memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable]
  exact Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf hfint

/-- **The two families are isometric.** -/
theorem dist_toLp_eq {f h : ℝ → ℝ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hh : MemLp h 2 (volume : Measure ℝ))
    (hfint : Integrable f (volume : Measure ℝ)) (hhint : Integrable h (volume : Measure ℝ))
    (hfh : MemLp (f - h) 2 (volume : Measure ℝ))
    (hfhint : Integrable (f - h) (volume : Measure ℝ)) :
    dist (hf.toLp f) (hh.toLp h)
      = dist ((memLp_fourier hf hfint).toLp _) ((memLp_fourier hh hhint).toLp _) := by
  have hL : dist (hf.toLp f) (hh.toLp h) ^ 2 = ∫ x : ℝ, (f x - h x) ^ 2 := by
    rw [dist_eq_norm, Cvs.WeilForm.EvennessSurvivesL2Limit.norm_toLp_sub_sq_real hf hh]
  have hR : dist ((memLp_fourier hf hfint).toLp _) ((memLp_fourier hh hhint).toLp _) ^ 2
      = ∫ ξ : ℝ, ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ - 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf h) ξ‖ ^ 2 := by
    rw [dist_eq_norm, ← Cvs.Upstream.PlancherelConvergenceTransfer.integral_sub_sq_eq_norm_sq
      (memLp_fourier hf hfint) (memLp_fourier hh hhint)]
  have heq : dist (hf.toLp f) (hh.toLp h) ^ 2
      = dist ((memLp_fourier hf hfint).toLp _) ((memLp_fourier hh hhint).toLp _) ^ 2 := by
    rw [hL, hR, Cvs.WeilForm.WindowTransformIsometry.integral_sub_sq_fourier hfh hfhint hfint hhint]
  have h1 : (0:ℝ) ≤ dist (hf.toLp f) (hh.toLp h) := dist_nonneg
  have h2 : (0:ℝ) ≤ dist ((memLp_fourier hf hfint).toLp _)
      ((memLp_fourier hh hhint).toLp _) := dist_nonneg
  nlinarith [heq, h1, h2]

end Cvs.WeilForm.TransformFamiliesIsometric
