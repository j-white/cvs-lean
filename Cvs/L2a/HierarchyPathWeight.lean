import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weights along a path of the hierarchy

The weight of a node of the `χ`-hierarchy is the product along its path of the two factors `g₁ = p₁/D⁰`,
`g₂ = p₂/D⁰`. With `|g_i| ≤ κ` and `|g_i'| ≤ κ'` on an interval, the weight of a path of length `n` is bounded by
`κⁿ` and its derivative by `n κⁿ⁻¹ κ'`, by the product rule along the path.
-/

namespace Cvs.L2a.HierarchyPathWeight

open Real Set

/-- The weight of a path: the product of `g₁` (for `true`) and `g₂` (for `false`) along it. -/
def pathWeight (g₁ g₂ : ℝ → ℝ) : List Bool → ℝ → ℝ
  | [] => fun _ => 1
  | true :: p => fun θ => g₁ θ * pathWeight g₁ g₂ p θ
  | false :: p => fun θ => g₂ θ * pathWeight g₁ g₂ p θ

/-- Appending a step multiplies the weight by that step's factor. -/
theorem pathWeight_append (g₁ g₂ : ℝ → ℝ) (p : List Bool) (b : Bool) (θ : ℝ) :
    pathWeight g₁ g₂ (p ++ [b]) θ = pathWeight g₁ g₂ p θ * (if b then g₁ θ else g₂ θ) := by
  induction p with
  | nil => cases b <;> simp [pathWeight]
  | cons a p ih => cases a <;> cases b <;> simp [pathWeight, ih] <;> ring

end Cvs.L2a.HierarchyPathWeight
