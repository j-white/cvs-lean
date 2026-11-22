import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form is translation invariant

`weilForm P R (f ∘ (· − c)) = weilForm P R f`: the self-convolution does not see the translation,
and the two pole moments pick up `e^{c/2}` and `e^{−c/2}`, whose product is one.
-/

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil Cvs.WeilForm.SelfConvolutionFunctional

namespace Cvs.WeilForm.WindowMomentsTranslationInvariant

/-- **The self-convolution of a translate.** -/
theorem selfConvolution_translate (f : ℝ → ℝ) (c u : ℝ) :
    selfConvolution (fun s => f (s - c)) u = selfConvolution f u := by
  unfold selfConvolution
  calc (∫ x : ℝ, (fun s => f (s - c)) x * (fun s => f (s - c)) (x + u))
      = ∫ x : ℝ, (fun y => f y * f (y + u)) (x - c) := by
        congr 1; funext x; simp only; rw [sub_add_eq_add_sub]
    _ = ∫ y : ℝ, f y * f (y + u) := by
        convert integral_sub_right_eq_self (fun y => f y * f (y + u)) c using 2
        infer_instance

/-- **The self-convolution of a translate, as a function.** -/
theorem selfConvolution_translate_fun (f : ℝ → ℝ) (c : ℝ) :
    selfConvolution (fun s => f (s - c)) = selfConvolution f :=
  funext fun u => selfConvolution_translate f c u

/-- **The pole moment `A` of a translate.** -/
theorem momentA_translate (f : ℝ → ℝ) (c : ℝ) :
    (∫ s : ℝ, f (s - c) * Real.exp (s / 2))
      = Real.exp (c / 2) * ∫ s : ℝ, f s * Real.exp (s / 2) := by
  calc (∫ s : ℝ, f (s - c) * Real.exp (s / 2))
      = ∫ s : ℝ, (fun y => Real.exp (c / 2) * (f y * Real.exp (y / 2))) (s - c) := by
        congr 1; funext s; simp only
        have h : Real.exp (s / 2) = Real.exp (c / 2) * Real.exp ((s - c) / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h]; ring
    _ = ∫ y : ℝ, Real.exp (c / 2) * (f y * Real.exp (y / 2)) := by
        convert integral_sub_right_eq_self (fun y => Real.exp (c / 2) * (f y * Real.exp (y / 2))) c using 2
        infer_instance
    _ = Real.exp (c / 2) * ∫ s : ℝ, f s * Real.exp (s / 2) := integral_const_mul _ _

/-- **The pole moment `M` of a translate.** -/
theorem momentM_translate (f : ℝ → ℝ) (c : ℝ) :
    (∫ s : ℝ, f (s - c) * Real.exp (-(s / 2)))
      = Real.exp (-(c / 2)) * ∫ s : ℝ, f s * Real.exp (-(s / 2)) := by
  calc (∫ s : ℝ, f (s - c) * Real.exp (-(s / 2)))
      = ∫ s : ℝ, (fun y => Real.exp (-(c / 2)) * (f y * Real.exp (-(y / 2)))) (s - c) := by
        congr 1; funext s; simp only
        have h : Real.exp (-(s / 2)) = Real.exp (-(c / 2)) * Real.exp (-((s - c) / 2)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h]; ring
    _ = ∫ y : ℝ, Real.exp (-(c / 2)) * (f y * Real.exp (-(y / 2))) := by
        convert integral_sub_right_eq_self
          (fun y => Real.exp (-(c / 2)) * (f y * Real.exp (-(y / 2)))) c using 2
        infer_instance
    _ = Real.exp (-(c / 2)) * ∫ s : ℝ, f s * Real.exp (-(s / 2)) := integral_const_mul _ _

/-- **Translation invariance of the window's Weil form.** -/
theorem weilForm_translate (P R : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    weilForm P R (fun s => f (s - c)) = weilForm P R f := by
  unfold weilForm
  rw [selfConvolution_translate_fun, momentA_translate, momentM_translate]
  have h : Real.exp (c / 2) * Real.exp (-(c / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination
    (2 * (∫ s : ℝ, f s * Real.exp (s / 2)) * (∫ s : ℝ, f s * Real.exp (-(s / 2)))) * h

end Cvs.WeilForm.WindowMomentsTranslationInvariant
