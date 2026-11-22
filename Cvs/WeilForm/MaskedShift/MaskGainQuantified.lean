import Mathlib
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real
open scoped InnerProductSpace NNReal

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.Operator

/-!
# What the mask buys, quantified

The trivial bound on an atom is `‖A_q‖ ≤ 2·Λ(q)/√q`: the two-hop operator `W = S + S*` is a
sum of two contractions.
-/

/-- **The Chebyshev factor's deficit from `2`, explicitly.**  Mathlib's
quadratic bound on the cosine, at `x = π/(m+1)`. -/
theorem chebFactor_le_two_sub (m : ℕ) :
    Cvs.Operator.chebFactor m ≤ 2 - 4 / ((m : ℝ) + 1) ^ 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have habs : |π / ((m : ℝ) + 1)| ≤ π := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hm1]
    nlinarith
  have h := Real.cos_le_one_sub_mul_cos_sq habs
  have hcalc : 2 / π ^ 2 * (π / ((m : ℝ) + 1)) ^ 2 = 2 / ((m : ℝ) + 1) ^ 2 := by
    field_simp
  rw [hcalc] at h
  have hsplit : (4 : ℝ) / ((m : ℝ) + 1) ^ 2 = 2 * (2 / ((m : ℝ) + 1) ^ 2) := by ring
  unfold Cvs.Operator.chebFactor
  linarith

/-- The mask strictly saves: `ν(m) < 2` for every chain length. -/
theorem chebFactor_lt_two (m : ℕ) : Cvs.Operator.chebFactor m < 2 := by
  have h := chebFactor_le_two_sub m
  have hpos : (0 : ℝ) < 4 / ((m : ℝ) + 1) ^ 2 := by positivity
  linarith

end Cvs.PrimeOperator
