import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Splitting a window at the edge of the layer

On `[p, q]`, `|∫ uv| ≤ √(∫u²)√(∫v²)` for continuous `u, v`, by completing the square; hence for `p ≤ X ≤ q`,
`|∫_p^q uv| ≤ √(∫_p^X u²)√(∫_p^X v²) + |∫_X^q uv|`: the layer `[p, X]` is charged by Cauchy–Schwarz to the masses,
and only `[X, q]` needs an oscillation envelope such as an earlier result.
-/

namespace Cvs.Prolate.LiouvilleGreen.LayerWindowSplit

open Real Set MeasureTheory intervalIntegral

/-- **Cauchy–Schwarz on an interval.** -/
theorem abs_integral_mul_le {u v : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q) (hu : ContinuousOn u (Icc p q))
    (hv : ContinuousOn v (Icc p q)) :
    |∫ x in p..q, u x * v x| ≤ √(∫ x in p..q, u x ^ 2) * √(∫ x in p..q, v x ^ 2) := by
  set A := ∫ x in p..q, u x ^ 2
  set B := ∫ x in p..q, u x * v x
  set C := ∫ x in p..q, v x ^ 2
  have ii : ∀ f : ℝ → ℝ, ContinuousOn f (Icc p q) → IntervalIntegrable f volume p q :=
    fun f hf => hf.intervalIntegrable_of_Icc hpq
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := fun t => by
    have h0 : 0 ≤ ∫ x in p..q, (u x - t * v x) ^ 2 :=
      intervalIntegral.integral_nonneg hpq fun x _ => sq_nonneg _
    have hexp : ∫ x in p..q, (u x - t * v x) ^ 2 = A - 2 * t * B + t ^ 2 * C := by
      have e : ∀ x, (u x - t * v x) ^ 2 = u x ^ 2 - 2 * t * (u x * v x) + t ^ 2 * v x ^ 2 := fun x => by ring
      simp_rw [e]
      have h1 : IntervalIntegrable (fun x => u x ^ 2) volume p q := ii _ (hu.pow 2)
      have h2 : IntervalIntegrable (fun x => 2 * t * (u x * v x)) volume p q :=
        ii _ (continuousOn_const.mul (hu.mul hv))
      have h3 : IntervalIntegrable (fun x => t ^ 2 * v x ^ 2) volume p q :=
        ii _ (continuousOn_const.mul (hv.pow 2))
      have s1 := intervalIntegral.integral_add (h1.sub h2) h3
      have s2 := intervalIntegral.integral_sub h1 h2
      have s3 : ∫ x in p..q, 2 * t * (u x * v x) = 2 * t * B :=
        intervalIntegral.integral_const_mul _ _
      have s4 : ∫ x in p..q, t ^ 2 * v x ^ 2 = t ^ 2 * C :=
        intervalIntegral.integral_const_mul _ _
      rw [s1, s2, s3, s4]
    linarith
  have hC0 : 0 ≤ C := intervalIntegral.integral_nonneg hpq fun x _ => sq_nonneg _
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hpq fun x _ => sq_nonneg _
  have hsq : B ^ 2 ≤ A * C := by
    rcases eq_or_lt_of_le hC0 with h | h
    · -- `C = 0` forces `B = 0`
      have hB : B = 0 := by
        by_contra hB
        have := key ((A + 1) / (2 * B))
        rw [← h] at this
        have e : A - 2 * ((A + 1) / (2 * B)) * B + ((A + 1) / (2 * B)) ^ 2 * 0 = -1 := by field_simp; ring
        linarith
      rw [hB, ← h]; simp
    · have := key (B / C)
      field_simp at this
      nlinarith
  rw [← Real.sqrt_mul hA0]
  exact Real.abs_le_sqrt hsq

end Cvs.Prolate.LiouvilleGreen.LayerWindowSplit
