import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# Dilation rescales the self-convolution

    selfConvolution (f (·/a)) u = a · selfConvolution f (u/a)      for `a > 0`

so the prime side, which reads the self-convolution at the fixed points `log k`, is moved by
dilation only through the self-convolution's own continuity.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.DilationSelfConvolution

/-- **Dilation rescales the self-convolution.** -/
theorem selfConvolution_dilate {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (u : ℝ) :
    selfConvolution (fun x => f (x / a)) u = a * selfConvolution f (u / a) := by
  have hG : ∀ s : ℝ, f (s / a) * f ((s + u) / a)
      = (fun t : ℝ => f t * f (t + u / a)) (s / a) := by
    intro s
    simp only
    congr 2
    field_simp
  have h1 : selfConvolution (fun x => f (x / a)) u
      = ∫ s : ℝ, (fun t : ℝ => f t * f (t + u / a)) (s / a) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    exact hG s
  rw [h1, MeasureTheory.Measure.integral_comp_div
    (fun t : ℝ => f t * f (t + u / a)) a, abs_of_pos ha, smul_eq_mul]
  rfl

/-- **The dilated function's energy scales.** -/
theorem integral_sq_dilate {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ x : ℝ, f (x / a) ^ 2) = a * ∫ x : ℝ, f x ^ 2 := by
  have h := MeasureTheory.Measure.integral_comp_div (fun t : ℝ => f t ^ 2) a
  rw [abs_of_pos ha, smul_eq_mul] at h
  exact h

end Cvs.WeilForm.DilationSelfConvolution
