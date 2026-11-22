import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Xi.CompletedZetaCriticalLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The completed zeta on the critical line, as a real integral

The integrand beyond one carries no imaginary part, so the integral is the image of a real one. The
completed zeta is half of it, and the factor two the pair of exponents contributed cancels against
that half.
-/

noncomputable section

open Set MeasureTheory Complex HurwitzZeta

namespace Cvs.Xi.CompletedZetaCriticalReal

/-- **`Λ₀` on the critical line is a real integral.** -/
theorem Λ₀_critical (τ : ℝ) :
    (hurwitzEvenFEPair 0).Λ₀ (((1 : ℂ) / 2 + (τ : ℂ) * I) / 2)
      = ((∫ x in Ioi (1 : ℝ),
            2 * (x ^ (-3 / 4 : ℝ) * Real.cos (τ / 2 * Real.log x)
              * (evenKernel 0 x - 1)) : ℝ) : ℂ) := by
  rw [Cvs.Xi.CompletedZetaCriticalLine.Λ₀_zero_combined, ← _root_.integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [Cvs.Xi.CompletedZetaCriticalLine.integrand_critical hx τ]
  push_cast
  ring

/-- **The completed zeta on the critical line.** -/
theorem completedRiemannZeta₀_critical (τ : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (τ : ℂ) * I)
      = ((∫ x in Ioi (1 : ℝ),
            x ^ (-3 / 4 : ℝ) * Real.cos (τ / 2 * Real.log x)
              * (evenKernel 0 x - 1) : ℝ) : ℂ) := by
  have h : completedRiemannZeta₀ ((1 : ℂ) / 2 + (τ : ℂ) * I)
      = ((hurwitzEvenFEPair 0).Λ₀ (((1 : ℂ) / 2 + (τ : ℂ) * I) / 2)) / 2 := rfl
  rw [h, Λ₀_critical τ, integral_const_mul]
  push_cast
  ring

end Cvs.Xi.CompletedZetaCriticalReal
