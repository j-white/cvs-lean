import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form is invariant under reflection

    weilForm P R (x ↦ f (−x)) = weilForm P R f

The self-convolution is even and reflection-invariant, so the archimedean and prime terms do
not move; reflection swaps the two pole functionals, and their product is symmetric.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.WeilFormReflection

/-- **The self-convolution is even.** -/
theorem selfConvolution_neg (f : ℝ → ℝ) (u : ℝ) :
    selfConvolution f (-u) = selfConvolution f u := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => f x * f (x + -u)) u
  have hg : selfConvolution f (-u) = ∫ x : ℝ, f x * f (x + -u) := rfl
  rw [hg, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [show x + u + -u = x by ring]
  exact mul_comm _ _

/-- **And it does not see a reflection.** -/
theorem selfConvolution_reflect (f : ℝ → ℝ) (u : ℝ) :
    selfConvolution (fun x => f (-x)) u = selfConvolution f u := by
  have h := integral_neg_eq_self (fun x : ℝ => f x * f (x + -u)) (volume : Measure ℝ)
  have hg : selfConvolution (fun x => f (-x)) u
      = ∫ x : ℝ, (fun y : ℝ => f y * f (y + -u)) (-x) := by
    unfold selfConvolution
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show -x + -u = -(x + u) by ring]
  rw [hg, h]
  exact selfConvolution_neg f u

/-- **Reflection swaps the two pole functionals.** -/
theorem integral_reflect_exp (f : ℝ → ℝ) :
    (∫ x : ℝ, f (-x) * Real.exp (x / 2)) = ∫ x : ℝ, f x * Real.exp (-(x / 2)) := by
  have h := integral_neg_eq_self (fun x : ℝ => f x * Real.exp (-(x / 2)))
    (volume : Measure ℝ)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [show -(-x / 2) = x / 2 by ring]

theorem integral_reflect_exp' (f : ℝ → ℝ) :
    (∫ x : ℝ, f (-x) * Real.exp (-(x / 2))) = ∫ x : ℝ, f x * Real.exp (x / 2) := by
  have h := integral_neg_eq_self (fun x : ℝ => f x * Real.exp (x / 2))
    (volume : Measure ℝ)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [show -x / 2 = -(x / 2) by ring]

/-- **The form is invariant under reflection.**  So its ground states split into even and
odd, and asking for an even one is asking about a genuine symmetry of the form. -/
theorem weilForm_reflect (P R : ℕ) (f : ℝ → ℝ) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (fun x => f (-x))
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  have hg : selfConvolution (fun x => f (-x)) = selfConvolution f :=
    funext fun u => selfConvolution_reflect f u
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, hg,
    integral_reflect_exp f, integral_reflect_exp' f]
  ring

end Cvs.WeilForm.WeilFormReflection
