import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's Weil form, as one functional of the self-convolution

    ∫ (f s − f (s+u))² ds = 2·(g 0 − g u),    g = selfConvolution f

so the archimedean Lévy energy, the prime side and the norm are all read off the same `g`.
The shift here is over `ℝ`, so this is the window's form and not a circle's.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SelfConvolutionFunctional

/-- **The shifted energy is the self-convolution's deficit.**  Everything the Weil form asks
about a test function goes through `g`. -/
theorem integral_sq_sub_eq {f : ℝ → ℝ} (u : ℝ)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hcross : Integrable fun s => f s * f (s + u)) :
    (∫ s : ℝ, (f s - f (s + u)) ^ 2)
      = 2 * (selfConvolution f 0 - selfConvolution f u) := by
  have hshift : Integrable fun s => (f (s + u)) ^ 2 := by
    have := hsq.comp_add_right u
    simpa using this
  have hexp : ∀ s : ℝ, (f s - f (s + u)) ^ 2
      = (f s) ^ 2 + (f (s + u)) ^ 2 - 2 * (f s * f (s + u)) := by
    intro s; ring
  have hsplit : (∫ s : ℝ, (f s - f (s + u)) ^ 2)
      = (∫ s : ℝ, ((f s) ^ 2 + (f (s + u)) ^ 2)) - ∫ s : ℝ, 2 * (f s * f (s + u)) := by
    calc (∫ s : ℝ, (f s - f (s + u)) ^ 2)
        = ∫ s : ℝ, (((f s) ^ 2 + (f (s + u)) ^ 2) - 2 * (f s * f (s + u))) :=
          integral_congr_ae (Filter.Eventually.of_forall hexp)
      _ = (∫ s : ℝ, ((f s) ^ 2 + (f (s + u)) ^ 2)) - ∫ s : ℝ, 2 * (f s * f (s + u)) :=
          integral_sub (hsq.add hshift) (hcross.const_mul 2)
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

/-- **The window's Weil form.**  Pole, archimedean Lévy energy, and the truncated prime side,
each a functional of the same self-convolution. -/
def weilForm (P R : ℕ) (f : ℝ → ℝ) : ℝ :=
  2 * (∫ s : ℝ, f s * Real.exp (s / 2)) * (∫ s : ℝ, f s * Real.exp (-(s / 2)))
    + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
      + ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * (selfConvolution f 0 - selfConvolution f (u / 2)))
    - primePowerSideTruncated P R (selfConvolution f)

/-- The three pieces, named. -/
theorem weilForm_eq (P R : ℕ) (f : ℝ → ℝ) :
    weilForm P R f
      = 2 * (∫ s : ℝ, f s * Real.exp (s / 2)) * (∫ s : ℝ, f s * Real.exp (-(s / 2)))
        + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution f 0
          + ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
              * (selfConvolution f 0 - selfConvolution f (u / 2)))
        - primePowerSideTruncated P R (selfConvolution f) := rfl

end Cvs.WeilForm.SelfConvolutionFunctional
