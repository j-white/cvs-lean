import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form is homogeneous of degree two

    weilForm P R (c·f) = c²·weilForm P R f

so the Rayleigh quotient is scale invariant and renormalising after an approximation step
costs nothing.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WeilFormHomogeneous

/-- **The self-convolution is quadratic.** -/
theorem selfConvolution_smul (c : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    selfConvolution (fun x => c * f x) u = c ^ 2 * selfConvolution f u := by
  have h1 : selfConvolution (fun x => c * f x) u
      = ∫ s : ℝ, (c * f s) * (c * f (s + u)) := rfl
  have h2 : selfConvolution f u = ∫ s : ℝ, f s * f (s + u) := rfl
  rw [h1, h2, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)

/-- **The prime side is linear in its argument.** -/
theorem primePowerSideTruncated_smul (P R : ℕ) (c : ℝ) (G : ℝ → ℝ) :
    primePowerSideTruncated P R (fun u => c * G u) = c * primePowerSideTruncated P R G := by
  rw [primePowerSideTruncated, primePowerSideTruncated, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **The form is homogeneous of degree two.** -/
theorem weilForm_smul (P R : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (fun x => c * f x)
      = c ^ 2 * Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  have hself : selfConvolution (fun x => c * f x) = fun u => c ^ 2 * selfConvolution f u :=
    funext fun u => selfConvolution_smul c f u
  have hA : (∫ s : ℝ, c * f s * Real.exp (s / 2)) = c * ∫ s : ℝ, f s * Real.exp (s / 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  have hM : (∫ s : ℝ, c * f s * Real.exp (-(s / 2)))
      = c * ∫ s : ℝ, f s * Real.exp (-(s / 2)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  have hlevy : (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (c ^ 2 * selfConvolution f 0 - c ^ 2 * selfConvolution f (u / 2)))
      = c ^ 2 * ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution f 0 - selfConvolution f (u / 2)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi
      (Filter.Eventually.of_forall fun u _ => by ring)
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, hself, hA, hM,
    primePowerSideTruncated_smul, hlevy]
  ring

end Cvs.WeilForm.WeilFormHomogeneous
