import Mathlib
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.WeilPositivityStatement

/-!
# The self-convolution is largest at the origin, and the Lévy energy is nonnegative

    |g u| ≤ g 0,    g = selfConvolution f

read off the two squares `∫ (f s ∓ f (s+u))² ≥ 0`, so every shift in `Cvs.WeilForm.SelfConvolutionFunctional`'s archimedean
term is charged a nonnegative amount and the term is bounded below by `archSymbol 0 · g 0`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SelfConvolutionMaximum

/-- **The other square.**  Companion to `Cvs.WeilForm.SelfConvolutionFunctional`'s difference identity. -/
theorem integral_sq_add_eq {f : ℝ → ℝ} (u : ℝ)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : Integrable fun s => f s * f (s + u)) :
    (∫ s : ℝ, (f s + f (s + u)) ^ 2)
      = 2 * (selfConvolution f 0 + selfConvolution f u) := by
  have hshift : Integrable fun s => (f (s + u)) ^ 2 := by
    have := hsq.comp_add_right u
    simpa using this
  have hexp : ∀ s : ℝ, (f s + f (s + u)) ^ 2
      = (f s) ^ 2 + (f (s + u)) ^ 2 + 2 * (f s * f (s + u)) := by
    intro s; ring
  have hsplit : (∫ s : ℝ, (f s + f (s + u)) ^ 2)
      = (∫ s : ℝ, ((f s) ^ 2 + (f (s + u)) ^ 2)) + ∫ s : ℝ, 2 * (f s * f (s + u)) := by
    calc (∫ s : ℝ, (f s + f (s + u)) ^ 2)
        = ∫ s : ℝ, (((f s) ^ 2 + (f (s + u)) ^ 2) + 2 * (f s * f (s + u))) :=
          integral_congr_ae (Filter.Eventually.of_forall hexp)
      _ = (∫ s : ℝ, ((f s) ^ 2 + (f (s + u)) ^ 2)) + ∫ s : ℝ, 2 * (f s * f (s + u)) :=
          integral_add (hsq.add hshift) (hcross.const_mul 2)
  rw [hsplit, integral_add hsq hshift, integral_const_mul]
  have hself : (∫ s : ℝ, (f (s + u)) ^ 2) = ∫ s : ℝ, (f s) ^ 2 :=
    integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun s : ℝ => (f s) ^ 2) u
  have hg0 : selfConvolution f 0 = ∫ s : ℝ, (f s) ^ 2 := by
    unfold selfConvolution
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [add_zero]
    ring
  have hgu : selfConvolution f u = ∫ s : ℝ, f s * f (s + u) := rfl
  rw [hself, hg0, hgu]
  ring

/-- **The shift never raises the self-convolution.** -/
theorem selfConvolution_le {f : ℝ → ℝ} (u : ℝ)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : Integrable fun s => f s * f (s + u)) :
    selfConvolution f u ≤ selfConvolution f 0 := by
  have hnn : 0 ≤ ∫ s : ℝ, (f s - f (s + u)) ^ 2 :=
    integral_nonneg fun s => sq_nonneg _
  rw [Cvs.WeilForm.SelfConvolutionFunctional.integral_sq_sub_eq u hsq hcross] at hnn
  linarith

/-- **And never lowers it past its negative.** -/
theorem neg_le_selfConvolution {f : ℝ → ℝ} (u : ℝ)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : Integrable fun s => f s * f (s + u)) :
    -selfConvolution f 0 ≤ selfConvolution f u := by
  have hnn : 0 ≤ ∫ s : ℝ, (f s + f (s + u)) ^ 2 :=
    integral_nonneg fun s => sq_nonneg _
  rw [integral_sq_add_eq u hsq hcross] at hnn
  linarith

/-- **The self-convolution is largest at the origin.** -/
theorem abs_selfConvolution_le {f : ℝ → ℝ} (u : ℝ)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : Integrable fun s => f s * f (s + u)) :
    |selfConvolution f u| ≤ selfConvolution f 0 :=
  abs_le.mpr ⟨neg_le_selfConvolution u hsq hcross, selfConvolution_le u hsq hcross⟩

end Cvs.WeilForm.SelfConvolutionMaximum
