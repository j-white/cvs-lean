import Mathlib
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# A nonnegative test has a nonnegative pole channel
-/

namespace Cvs.Detection

open Complex MeasureTheory
open scoped Real

/-- The character at `ξ = −i/2` is `e^{−s/2}`. -/
theorem char_neg_half (s : ℝ) :
    Complex.exp (-((s : ℂ) * (-(I / 2))) * I) = ((Real.exp (-s / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((s : ℂ) / 2) * Complex.I_sq

/-- The character at `ξ = i/2` is `e^{s/2}`. -/
theorem char_pos_half (s : ℝ) :
    Complex.exp (-((s : ℂ) * (I / 2)) * I) = ((Real.exp (s / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(s : ℂ) / 2) * Complex.I_sq

theorem windowTransform_at_neg_half (L : ℝ) (f : ℝ → ℝ) :
    Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) (-(I / 2))
      = ((∫ s in (0 : ℝ)..L, Real.exp (-s / 2) * f s : ℝ) : ℂ) := by
  rw [Cvs.Detection.windowTransform, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [char_neg_half]
  push_cast
  ring

theorem windowTransform_at_pos_half (L : ℝ) (f : ℝ → ℝ) :
    Cvs.Detection.windowTransform L (fun s => ((f s : ℝ) : ℂ)) (I / 2)
      = ((∫ s in (0 : ℝ)..L, Real.exp (s / 2) * f s : ℝ) : ℂ) := by
  rw [Cvs.Detection.windowTransform, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [char_pos_half]
  push_cast
  ring

end Cvs.Detection
