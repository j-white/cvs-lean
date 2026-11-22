import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real

namespace Cvs.Operator

/-- `ν m = 2 cos(π/(m+1))`. -/
noncomputable def chebFactor (m : ℕ) : ℝ := 2 * Real.cos (π / (m + 1 : ℝ))

theorem chebFactor_strictMono : StrictMono chebFactor := by
  intro a b hab
  unfold chebFactor
  have ha : (0:ℝ) < (a : ℝ) + 1 := by positivity
  have hcast : (a : ℝ) + 1 < (b : ℝ) + 1 := by
    have := (Nat.cast_lt (α := ℝ)).mpr hab
    linarith
  have hdiv : π / ((b : ℝ) + 1) < π / ((a : ℝ) + 1) :=
    div_lt_div_of_pos_left Real.pi_pos ha hcast
  have hb0 : (0:ℝ) ≤ π / ((b : ℝ) + 1) := by positivity
  have hale : π / ((a : ℝ) + 1) ≤ π := by
    rw [div_le_iff₀ ha]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) a]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi hb0 hale hdiv
  linarith

/-- `ν 2 = 1`: the unit that normalises the scale. -/
theorem chebFactor_two : chebFactor 2 = 1 := by
  have h3 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  unfold chebFactor
  rw [h3, Real.cos_pi_div_three]
  norm_num

theorem chebFactor_monotone : Monotone chebFactor := chebFactor_strictMono.monotone

end Cvs.Operator
