import Mathlib
import Cvs.Finite.WindowModeTransformClosed
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# A window cosine combination's transform

    𝓛 (1_{(0,L]}·modeSum) z = 2z·e^{izL/2}·sin(zL/2)·∑ₙ aₙ/(z² − (2πn/L)²)

a nonvanishing factor, times `sin(zL/2)`, times a partial-fraction sum.
-/

set_option maxHeartbeats 3200000

noncomputable section

open Complex MeasureTheory

namespace Cvs.Finite.WindowCosineSumTransform

/-- The transform, as an integral over the window. -/
theorem fourierLaplace_indicator {L : ℝ} (hL : 0 ≤ L) (F : ℝ → ℝ) (z : ℂ)
    (hint : Integrable (fun t : ℝ =>
      ((Set.indicator (Set.Ioc (0:ℝ) L) F t : ℝ) : ℂ)
        * Complex.exp (Complex.I * z * (t : ℂ))) (volume : Measure ℝ)) :
    FourierLaplace.fourierLaplace
        (Cvs.WeilForm.SelfConvolutionTransform.cf (Set.indicator (Set.Ioc (0:ℝ) L) F)) z
      = ∫ t in (0:ℝ)..L, ((F t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ)) := by
  rw [FourierLaplace.fourierLaplace]
  rw [show (fun t : ℝ => Cvs.WeilForm.SelfConvolutionTransform.cf
        (Set.indicator (Set.Ioc (0:ℝ) L) F) t * Complex.exp (Complex.I * z * (t : ℂ)))
      = Set.indicator (Set.Ioc (0:ℝ) L)
          (fun t : ℝ => ((F t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))) from ?_]
  · rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hL]
  · funext t
    simp only [Cvs.WeilForm.SelfConvolutionTransform.cf]
    by_cases ht : t ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      simp

/-- **The transform of a window cosine combination.** -/
theorem fourierLaplace_modeSum {L : ℝ} (hL : 0 < L) (s : Finset ℕ) (a : ℕ → ℝ) {z : ℂ}
    (hz : ∀ n ∈ s, z ^ 2 ≠ ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2)
    (hint : Integrable (fun t : ℝ =>
      ((Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a) t : ℝ) : ℂ)
        * Complex.exp (Complex.I * z * (t : ℂ))) (volume : Measure ℝ)) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Set.indicator (Set.Ioc (0:ℝ) L) (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a))) z
      = 2 * z * Complex.exp (Complex.I * z * (L : ℂ) / 2) * Complex.sin (z * (L : ℂ) / 2)
          * ∑ n ∈ s, ((a n : ℝ) : ℂ)
              / (z ^ 2 - ((2 * Real.pi * n / L : ℝ) : ℂ) ^ 2) := by
  classical
  rw [fourierLaplace_indicator hL.le _ z hint]
  -- expand the mode sum inside the integral
  have hpt : ∀ t : ℝ, ((Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a t : ℝ) : ℂ)
      * Complex.exp (Complex.I * z * (t : ℂ))
      = ∑ n ∈ s, ((a n : ℝ) : ℂ)
          * (((Real.cos (2 * Real.pi * n / L * t) : ℝ) : ℂ)
            * Complex.exp (Complex.I * z * (t : ℂ))) := by
    intro t
    rw [Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_finsetSum (fun n _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_const_mul,
    Cvs.Finite.WindowModeTransformClosed.integral_cos_mode (ne_of_gt hL) n (hz n hn)]
  field_simp

end Cvs.Finite.WindowCosineSumTransform
