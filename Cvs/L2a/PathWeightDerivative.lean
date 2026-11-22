import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightTwoConstants

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The derivative of a path weight as an explicit function

`pathWeight' g₁ g₂ g₁' g₂' p` is the product-rule derivative of `pathWeight g₁ g₂ p` (Cvs.L2a.HierarchyPathWeight): `0` on the empty path,
`g₁' · pw p + g₁ · pw' p` after a true step and `g₂' · pw p + g₂ · pw' p` after a false step. It is the derivative
wherever the factors are differentiable, is continuous when they are, and is bounded by
`(k κ₁'/κ₁ + l κ₂'/κ₂) κ₁^k κ₂^l` (Cvs.L2a.PathWeightTwoConstants) with `k, l` the numbers of true and false steps.
-/

namespace Cvs.L2a.PathWeightDerivative

open Real Set Cvs.L2a.HierarchyPathWeight Cvs.L2a.PathWeightTwoConstants

/-- The product-rule derivative of a path weight. -/
noncomputable def pathWeight' (g₁ g₂ g₁' g₂' : ℝ → ℝ) : List Bool → ℝ → ℝ
  | [] => fun _ => 0
  | true :: p => fun θ => g₁' θ * pathWeight g₁ g₂ p θ + g₁ θ * pathWeight' g₁ g₂ g₁' g₂' p θ
  | false :: p => fun θ => g₂' θ * pathWeight g₁ g₂ p θ + g₂ θ * pathWeight' g₁ g₂ g₁' g₂' p θ

/-- **It is the derivative** wherever `g₁`, `g₂` are differentiable with derivatives `g₁'`, `g₂'`. -/
theorem hasDerivAt_pathWeight' {g₁ g₂ g₁' g₂' : ℝ → ℝ} {s : Set ℝ}
    (hd₁ : ∀ θ ∈ s, HasDerivAt g₁ (g₁' θ) θ) (hd₂ : ∀ θ ∈ s, HasDerivAt g₂ (g₂' θ) θ) (p : List Bool) :
    ∀ θ ∈ s, HasDerivAt (pathWeight g₁ g₂ p) (pathWeight' g₁ g₂ g₁' g₂' p θ) θ := by
  induction p with
  | nil => intro θ _; simp only [pathWeight, pathWeight']; exact hasDerivAt_const θ (1 : ℝ)
  | cons a p ih =>
    intro θ hθ
    cases a
    · have := (hd₂ θ hθ).fun_mul (ih θ hθ)
      simpa [pathWeight, pathWeight'] using this
    · have := (hd₁ θ hθ).fun_mul (ih θ hθ)
      simpa [pathWeight, pathWeight'] using this

/-- **Continuity** of the path weight and its derivative on a set where the factors are continuous. -/
theorem continuousOn_pathWeight {g₁ g₂ : ℝ → ℝ} {s : Set ℝ} (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (p : List Bool) : ContinuousOn (pathWeight g₁ g₂ p) s := by
  induction p with
  | nil => simp only [pathWeight]; exact continuousOn_const
  | cons a p ih => cases a <;> simp only [pathWeight] <;> [exact h₂.mul ih; exact h₁.mul ih]

theorem continuousOn_pathWeight' {g₁ g₂ g₁' g₂' : ℝ → ℝ} {s : Set ℝ} (h₁ : ContinuousOn g₁ s)
    (h₂ : ContinuousOn g₂ s) (h₁' : ContinuousOn g₁' s) (h₂' : ContinuousOn g₂' s) (p : List Bool) :
    ContinuousOn (pathWeight' g₁ g₂ g₁' g₂' p) s := by
  induction p with
  | nil => simp only [pathWeight']; exact continuousOn_const
  | cons a p ih =>
    cases a
    · simp only [pathWeight']
      exact (h₂'.mul (continuousOn_pathWeight h₁ h₂ p)).add (h₂.mul ih)
    · simp only [pathWeight']
      exact (h₁'.mul (continuousOn_pathWeight h₁ h₂ p)).add (h₁.mul ih)

/-- **The bound on the derivative**: `|pathWeight' p| ≤ (k κ₁'/κ₁ + l κ₂'/κ₂) κ₁^k κ₂^l` for `κ₁, κ₂ > 0`. -/
theorem abs_pathWeight'_le {g₁ g₂ g₁' g₂' : ℝ → ℝ} {κ₁ κ₂ κ₁' κ₂' : ℝ} {s : Set ℝ}
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hκ₁' : 0 ≤ κ₁') (hκ₂' : 0 ≤ κ₂')
    (h₁ : ∀ θ ∈ s, |g₁ θ| ≤ κ₁) (h₂ : ∀ θ ∈ s, |g₂ θ| ≤ κ₂)
    (h₁' : ∀ θ ∈ s, |g₁' θ| ≤ κ₁') (h₂' : ∀ θ ∈ s, |g₂' θ| ≤ κ₂') (p : List Bool) :
    ∀ θ ∈ s, |pathWeight' g₁ g₂ g₁' g₂' p θ|
      ≤ (ktrue p * (κ₁' / κ₁) + lfalse p * (κ₂' / κ₂)) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) := by
  induction p with
  | nil => intro θ _; simp [pathWeight', ktrue, lfalse]
  | cons a p ih =>
    intro θ hθ
    have hw := abs_pathWeight_le₂ hκ₁.le hκ₂.le h₁ h₂ p θ hθ
    have hne₁ := hκ₁.ne'
    have hne₂ := hκ₂.ne'
    cases a
    · simp only [pathWeight', ktrue_cons_false, lfalse_cons_false]
      have hA : |g₂' θ * pathWeight g₁ g₂ p θ| ≤ κ₂' * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) := by
        rw [abs_mul]; exact mul_le_mul (h₂' θ hθ) hw (abs_nonneg _) hκ₂'
      have hB : |g₂ θ * pathWeight' g₁ g₂ g₁' g₂' p θ|
          ≤ κ₂ * ((ktrue p * (κ₁' / κ₁) + lfalse p * (κ₂' / κ₂)) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)) := by
        rw [abs_mul]; exact mul_le_mul (h₂ θ hθ) (ih θ hθ) (abs_nonneg _) hκ₂.le
      refine le_trans (abs_add_le _ _) (le_trans (add_le_add hA hB) (le_of_eq ?_))
      push_cast; field_simp; ring
    · simp only [pathWeight', ktrue_cons_true, lfalse_cons_true]
      have hA : |g₁' θ * pathWeight g₁ g₂ p θ| ≤ κ₁' * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) := by
        rw [abs_mul]; exact mul_le_mul (h₁' θ hθ) hw (abs_nonneg _) hκ₁'
      have hB : |g₁ θ * pathWeight' g₁ g₂ g₁' g₂' p θ|
          ≤ κ₁ * ((ktrue p * (κ₁' / κ₁) + lfalse p * (κ₂' / κ₂)) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)) := by
        rw [abs_mul]; exact mul_le_mul (h₁ θ hθ) (ih θ hθ) (abs_nonneg _) hκ₁.le
      refine le_trans (abs_add_le _ _) (le_trans (add_le_add hA hB) (le_of_eq ?_))
      push_cast; field_simp; ring

end Cvs.L2a.PathWeightDerivative
