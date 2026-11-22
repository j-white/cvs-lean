import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyPathWeight

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The path weights with two constants

With `|g₁| ≤ κ₁`, `|g₂| ≤ κ₂` and `|g₁'| ≤ κ₁'`, `|g₂'| ≤ κ₂'` on a set, the weight of a path with `k` true steps and
`l` false steps is bounded by `κ₁^k κ₂^l` and its derivative by `(k κ₁'/κ₁ + l κ₂'/κ₂) κ₁^k κ₂^l`: the sup
norms of the path weights (Cvs.L2a.HierarchyPathWeight) with the two factors kept apart, so the passed fractions of the project are
`t κ₁ χ` and `s κ₂ χ` separately.
-/

namespace Cvs.L2a.PathWeightTwoConstants

open Real Set Cvs.L2a.HierarchyPathWeight

/-- The number of true and false steps of a path. -/
def ktrue (p : List Bool) : ℕ := p.count true
def lfalse (p : List Bool) : ℕ := p.count false

theorem ktrue_cons_true (p : List Bool) : ktrue (true :: p) = ktrue p + 1 := by simp [ktrue]
theorem ktrue_cons_false (p : List Bool) : ktrue (false :: p) = ktrue p := by simp [ktrue]
theorem lfalse_cons_true (p : List Bool) : lfalse (true :: p) = lfalse p := by simp [lfalse]
theorem lfalse_cons_false (p : List Bool) : lfalse (false :: p) = lfalse p + 1 := by simp [lfalse]

/-- **The weight of a path with two constants**: `|pathWeight p| ≤ κ₁^k κ₂^l`. -/
theorem abs_pathWeight_le₂ {g₁ g₂ : ℝ → ℝ} {κ₁ κ₂ : ℝ} {s : Set ℝ} (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (h₁ : ∀ θ ∈ s, |g₁ θ| ≤ κ₁) (h₂ : ∀ θ ∈ s, |g₂ θ| ≤ κ₂) (p : List Bool) :
    ∀ θ ∈ s, |pathWeight g₁ g₂ p θ| ≤ κ₁ ^ ktrue p * κ₂ ^ lfalse p := by
  induction p with
  | nil => intro θ _; simp [pathWeight, ktrue, lfalse]
  | cons a p ih =>
    intro θ hθ
    cases a
    · simp only [pathWeight, abs_mul, ktrue_cons_false, lfalse_cons_false, pow_succ]
      calc |g₂ θ| * |pathWeight g₁ g₂ p θ| ≤ κ₂ * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) :=
            mul_le_mul (h₂ θ hθ) (ih θ hθ) (abs_nonneg _) hκ₂
        _ = κ₁ ^ ktrue p * (κ₂ ^ lfalse p * κ₂) := by ring
    · simp only [pathWeight, abs_mul, ktrue_cons_true, lfalse_cons_true, pow_succ]
      calc |g₁ θ| * |pathWeight g₁ g₂ p θ| ≤ κ₁ * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) :=
            mul_le_mul (h₁ θ hθ) (ih θ hθ) (abs_nonneg _) hκ₁
        _ = κ₁ ^ ktrue p * κ₁ * κ₂ ^ lfalse p := by ring

end Cvs.L2a.PathWeightTwoConstants
