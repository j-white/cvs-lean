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
# The binary hierarchy sums with a level cost depending on the depth

For `x` on the paths of a binary tree with `x p ≤ E |p| + ρ₁ x(p ++ [true]) + ρ₂ x(p ++ [false])` below depth `N`
and `x p ≤ X` at depth `N`, `x [] ≤ Σ_{j<N} (ρ₁ + ρ₂)^j E j + (ρ₁ + ρ₂)^N X`: the project sum (an earlier result) with the cost
of a level allowed to grow with the depth, as the derivatives of the path weights do (Cvs.L2a.PathWeightTwoConstants).
-/

namespace Cvs.Upstream.BinaryTreeDepthSum

open Finset

/-- **The tree sum with a depth-dependent level cost.** -/
theorem tree_sum_depth {x : List Bool → ℝ} {E : ℕ → ℝ} {ρ₁ ρ₂ X : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (N : ℕ)
    (hstep : ∀ p : List Bool, p.length < N → x p ≤ E p.length + ρ₁ * x (p ++ [true]) + ρ₂ * x (p ++ [false]))
    (hleaf : ∀ p : List Bool, p.length = N → x p ≤ X) :
    x [] ≤ (∑ j ∈ range N, (ρ₁ + ρ₂) ^ j * E j) + (ρ₁ + ρ₂) ^ N * X := by
  have key : ∀ d : ℕ, d ≤ N → ∀ p : List Bool, p.length + d = N →
      x p ≤ (∑ j ∈ range d, (ρ₁ + ρ₂) ^ j * E (p.length + j)) + (ρ₁ + ρ₂) ^ d * X := by
    intro d
    induction d with
    | zero =>
      intro _ p hp
      simp only [add_zero] at hp
      simpa using hleaf p hp
    | succ d ih =>
      intro hd p hp
      have hlt : p.length < N := by omega
      have h1 := ih (by omega) (p ++ [true]) (by simp; omega)
      have h2 := ih (by omega) (p ++ [false]) (by simp; omega)
      have hs := hstep p hlt
      simp only [List.length_append, List.length_singleton] at h1 h2
      have e : (∑ j ∈ range (d + 1), (ρ₁ + ρ₂) ^ j * E (p.length + j)) + (ρ₁ + ρ₂) ^ (d + 1) * X
          = E p.length + (ρ₁ + ρ₂) * ((∑ j ∈ range d, (ρ₁ + ρ₂) ^ j * E (p.length + 1 + j)) + (ρ₁ + ρ₂) ^ d * X) := by
        rw [Finset.sum_range_succ', pow_zero, one_mul, add_zero, mul_add, Finset.mul_sum, pow_succ]
        have : ∀ j, (ρ₁ + ρ₂) * ((ρ₁ + ρ₂) ^ j * E (p.length + 1 + j)) = (ρ₁ + ρ₂) ^ (j + 1) * E (p.length + (j + 1)) := by
          intro j; rw [pow_succ, add_assoc, add_comm 1 j]; ring
        simp only [this]; ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left h1 hρ₁, mul_le_mul_of_nonneg_left h2 hρ₂]
  simpa using key N le_rfl [] (by simp)

end Cvs.Upstream.BinaryTreeDepthSum
