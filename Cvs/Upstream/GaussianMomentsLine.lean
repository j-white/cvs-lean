import Mathlib
import Cvs.Upstream.PolyGaussianIntegrable

/-!
# The moments on the line, and `an earlier result`'s bracket made explicit

`GaussianSecondMoment` and `GaussianMomentRecursion` evaluated the even moments on `(0, ∞)`; `an earlier result`'s bracket is stated over `ℝ`.
-/

namespace Cvs.Moments

open MeasureTheory
open scoped Real

/-- The even moments on the line are twice those on the half-line. -/
theorem moment_real {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    (∫ y : ℝ, y ^ (2 * m) * Real.exp (-lam * y ^ 2))
      = 2 * ∫ y in Set.Ioi (0 : ℝ), y ^ (2 * m) * Real.exp (-lam * y ^ 2) := by
  have hI := Cvs.Moments.integrable_pow_mul_gaussian hlam m
  have heven : ∀ y : ℝ, (-y) ^ (2 * m) * Real.exp (-lam * (-y) ^ 2)
      = y ^ (2 * m) * Real.exp (-lam * y ^ 2) := by
    intro y
    rw [neg_pow, neg_sq]
    simp [pow_mul]
  have h1 : (∫ y in Set.Ioi (0 : ℝ), y ^ (2 * m) * Real.exp (-lam * y ^ 2))
      = ∫ y in Set.Iic (0 : ℝ), y ^ (2 * m) * Real.exp (-lam * y ^ 2) := by
    have h := integral_comp_neg_Ioi (0 : ℝ)
      (fun y : ℝ => y ^ (2 * m) * Real.exp (-lam * y ^ 2))
    simp only [neg_zero] at h
    rw [← h]
    exact (setIntegral_congr_fun measurableSet_Ioi fun y _ => (heven y).symm)
  have h2 := integral_add_compl (μ := volume) (s := Set.Iic (0 : ℝ))
    measurableSet_Iic hI
  rw [Set.compl_Iic] at h2
  rw [← h2, ← h1]
  ring

end Cvs.Moments
