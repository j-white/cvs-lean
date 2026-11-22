import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form is invariant under translation

    weilForm P R (x ↦ f (x + c)) = weilForm P R f

The self-convolution does not move, and translation scales the two pole functionals by
reciprocal factors, so the support may sit on any interval of length `L`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WindowFormTranslationInvariant

/-- **The self-convolution is translation invariant.** -/
theorem selfConvolution_translate (f : ℝ → ℝ) (c u : ℝ) :
    selfConvolution (fun x => f (x + c)) u = selfConvolution f u := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => f y * f (y + u)) c
  have hg : selfConvolution (fun x => f (x + c)) u
      = ∫ x : ℝ, (fun y : ℝ => f y * f (y + u)) (x + c) := by
    unfold selfConvolution
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x + u + c = x + c + u by ring]
  rw [hg, h]
  rfl

/-- **Translation scales the pole functional.** -/
theorem integral_translate_exp (f : ℝ → ℝ) (c : ℝ) :
    (∫ x : ℝ, f (x + c) * Real.exp (x / 2))
      = Real.exp (-(c / 2)) * ∫ x : ℝ, f x * Real.exp (x / 2) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => f y * Real.exp ((y - c) / 2)) c
  have hg : (∫ x : ℝ, f (x + c) * Real.exp (x / 2))
      = ∫ x : ℝ, (fun y : ℝ => f y * Real.exp ((y - c) / 2)) (x + c) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x + c - c = x by ring]
  rw [hg, h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [show (x - c) / 2 = -(c / 2) + x / 2 by ring, Real.exp_add]
  ring

/-- **The other one is scaled by the reciprocal.** -/
theorem integral_translate_exp' (f : ℝ → ℝ) (c : ℝ) :
    (∫ x : ℝ, f (x + c) * Real.exp (-(x / 2)))
      = Real.exp (c / 2) * ∫ x : ℝ, f x * Real.exp (-(x / 2)) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => f y * Real.exp (-((y - c) / 2))) c
  have hg : (∫ x : ℝ, f (x + c) * Real.exp (-(x / 2)))
      = ∫ x : ℝ, (fun y : ℝ => f y * Real.exp (-((y - c) / 2))) (x + c) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x + c - c = x by ring]
  rw [hg, h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [show -((x - c) / 2) = c / 2 + -(x / 2) by ring, Real.exp_add]
  ring

/-- **The form is translation invariant.** -/
theorem weilForm_translate (P R : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (fun x => f (x + c))
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  have hg : selfConvolution (fun x => f (x + c)) = selfConvolution f :=
    funext fun u => selfConvolution_translate f c u
  have hrecip : Real.exp (-(c / 2)) * Real.exp (c / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, hg,
    integral_translate_exp f c, integral_translate_exp' f c]
  have hmul : 2 * (Real.exp (-(c / 2)) * ∫ x : ℝ, f x * Real.exp (x / 2))
        * (Real.exp (c / 2) * ∫ x : ℝ, f x * Real.exp (-(x / 2)))
      = (Real.exp (-(c / 2)) * Real.exp (c / 2))
        * (2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * ∫ x : ℝ, f x * Real.exp (-(x / 2))) := by
    ring
  rw [hmul, hrecip, one_mul]

end Cvs.WeilForm.WindowFormTranslationInvariant
