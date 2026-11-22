import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyPathWeight
import Cvs.L2a.PathWeightDerivative
import Cvs.L2a.PathWeightTwoConstants

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weight of a node: a cutoff times a path weight, and its sup bounds

`σ_p = σ · pathWeight p` is `C¹` with derivative `σ' pw + σ pw'` (Cvs.L2a.PathWeightDerivative), vanishes where `σ` does, and with
`|σ| ≤ 1`, `|σ'| ≤ S'`, `|g_i| ≤ κ_i`, `|g_i'| ≤ κ_i'` on the set, `|σ_p| ≤ κ₁^l κ₂^k` and
`|σ_p' g_i + σ_p g_i'| ≤ D_i(k, l) κ₁^l κ₂^k` with `D_i = (S' + l κ₁'/κ₁ + k κ₂'/κ₂) κ_i + κ_i'`, `l, k` the true and
false steps; so `(σ_p' g_i + σ_p g_i')² P ≤ D_i² κ₁^{2l} κ₂^{2k} P_max`: the constants `C_i` of the node cost (Cvs.L2a.BoundaryFreeNodeCostModes).
-/

namespace Cvs.L2a.HierarchyNodeWeight

open Real Set Cvs.L2a.HierarchyPathWeight Cvs.L2a.PathWeightTwoConstants Cvs.L2a.PathWeightDerivative

/-- The growth factor of the derivative of a node weight at depth `(k, l)`. -/
noncomputable def growth (S' κ₁ κ₂ κ₁' κ₂' : ℝ) (k l : ℕ) : ℝ := S' + l * (κ₁' / κ₁) + k * (κ₂' / κ₂)

/-- **The node weight is `C¹`** with derivative `σ' pw + σ pw'`, and vanishes where `σ` does. -/
theorem hasDerivAt_node_weight {σ σ' g₁ g₂ g₁' g₂' : ℝ → ℝ} {s : Set ℝ}
    (hσ : ∀ θ ∈ s, HasDerivAt σ (σ' θ) θ)
    (hd₁ : ∀ θ ∈ s, HasDerivAt g₁ (g₁' θ) θ) (hd₂ : ∀ θ ∈ s, HasDerivAt g₂ (g₂' θ) θ) (p : List Bool) :
    ∀ θ ∈ s, HasDerivAt (fun θ => σ θ * pathWeight g₁ g₂ p θ)
      (σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) θ := fun θ hθ =>
  (hσ θ hθ).fun_mul (hasDerivAt_pathWeight' hd₁ hd₂ p θ hθ)

/-- **The sup bounds of a node weight and of its `f u` coefficients.** -/
theorem node_weight_bounds {σ σ' g₁ g₂ g₁' g₂' : ℝ → ℝ} {S' κ₁ κ₂ κ₁' κ₂' : ℝ} {s : Set ℝ}
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hκ₁' : 0 ≤ κ₁') (hκ₂' : 0 ≤ κ₂') (hS' : 0 ≤ S')
    (hσ1 : ∀ θ ∈ s, |σ θ| ≤ 1) (hσ' : ∀ θ ∈ s, |σ' θ| ≤ S')
    (h₁ : ∀ θ ∈ s, |g₁ θ| ≤ κ₁) (h₂ : ∀ θ ∈ s, |g₂ θ| ≤ κ₂)
    (h₁' : ∀ θ ∈ s, |g₁' θ| ≤ κ₁') (h₂' : ∀ θ ∈ s, |g₂' θ| ≤ κ₂') (p : List Bool) :
    (∀ θ ∈ s, |σ θ * pathWeight g₁ g₂ p θ| ≤ κ₁ ^ ktrue p * κ₂ ^ lfalse p) ∧
    (∀ θ ∈ s, |σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ|
      ≤ growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)) ∧
    (∀ θ ∈ s, |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g₁ θ
        + σ θ * pathWeight g₁ g₂ p θ * g₁' θ|
      ≤ (growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) * κ₁ + κ₁') * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)) ∧
    (∀ θ ∈ s, |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g₂ θ
        + σ θ * pathWeight g₁ g₂ p θ * g₂' θ|
      ≤ (growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) * κ₂ + κ₂') * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)) := by
  have hw := abs_pathWeight_le₂ hκ₁.le hκ₂.le h₁ h₂ p
  have hw' := abs_pathWeight'_le hκ₁ hκ₂ hκ₁' hκ₂' h₁ h₂ h₁' h₂' p
  have hK : 0 ≤ κ₁ ^ ktrue p * κ₂ ^ lfalse p := by positivity
  have hG : 0 ≤ growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) := by
    unfold growth; positivity
  have hA : ∀ θ ∈ s, |σ θ * pathWeight g₁ g₂ p θ| ≤ κ₁ ^ ktrue p * κ₂ ^ lfalse p := fun θ hθ => by
    rw [abs_mul]
    calc |σ θ| * |pathWeight g₁ g₂ p θ| ≤ 1 * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) :=
          mul_le_mul (hσ1 θ hθ) (hw θ hθ) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hB : ∀ θ ∈ s, |σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ|
      ≤ growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) := fun θ hθ => by
    have h1 : |σ' θ * pathWeight g₁ g₂ p θ| ≤ S' * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) := by
      rw [abs_mul]; exact mul_le_mul (hσ' θ hθ) (hw θ hθ) (abs_nonneg _) hS'
    have h2 : |σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ|
        ≤ (ktrue p * (κ₁' / κ₁) + lfalse p * (κ₂' / κ₂)) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) := by
      rw [abs_mul]
      calc |σ θ| * |pathWeight' g₁ g₂ g₁' g₂' p θ|
          ≤ 1 * ((ktrue p * (κ₁' / κ₁) + lfalse p * (κ₂' / κ₂)) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)) :=
            mul_le_mul (hσ1 θ hθ) (hw' θ hθ) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add h1 h2) (le_of_eq ?_))
    unfold growth; ring
  refine ⟨hA, hB, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have h1 : |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g₁ θ|
        ≤ growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) * κ₁ := by
      rw [abs_mul]; exact mul_le_mul (hB θ hθ) (h₁ θ hθ) (abs_nonneg _) (by positivity)
    have h2 : |σ θ * pathWeight g₁ g₂ p θ * g₁' θ| ≤ κ₁ ^ ktrue p * κ₂ ^ lfalse p * κ₁' := by
      rw [abs_mul]; exact mul_le_mul (hA θ hθ) (h₁' θ hθ) (abs_nonneg _) hK
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add h1 h2) (le_of_eq ?_))
    ring
  · have h1 : |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g₂ θ|
        ≤ growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) * (κ₁ ^ ktrue p * κ₂ ^ lfalse p) * κ₂ := by
      rw [abs_mul]; exact mul_le_mul (hB θ hθ) (h₂ θ hθ) (abs_nonneg _) (by positivity)
    have h2 : |σ θ * pathWeight g₁ g₂ p θ * g₂' θ| ≤ κ₁ ^ ktrue p * κ₂ ^ lfalse p * κ₂' := by
      rw [abs_mul]; exact mul_le_mul (hA θ hθ) (h₂' θ hθ) (abs_nonneg _) hK
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add h1 h2) (le_of_eq ?_))
    ring

/-- The depth factor of the derivative of a node weight, without `S'`. -/
noncomputable def grow0 (κ₁ κ₂ κ₁' κ₂' : ℝ) (k l : ℕ) : ℝ := l * (κ₁' / κ₁) + k * (κ₂' / κ₂)

/-- **The `f u` coefficients of a node weight, pointwise in the factors**: for `S' > 0`,
`|σ_p' g_i + σ_p g_i'| ≤ (1 + grow0/S') κ₁^l κ₂^k (S'|g_i| + |g_i'|)`. -/
theorem node_weight_coeff_pointwise {σ σ' g₁ g₂ g₁' g₂' : ℝ → ℝ} {S' κ₁ κ₂ κ₁' κ₂' : ℝ} {s : Set ℝ}
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hκ₁' : 0 ≤ κ₁') (hκ₂' : 0 ≤ κ₂') (hS' : 0 < S')
    (hσ1 : ∀ θ ∈ s, |σ θ| ≤ 1) (hσ' : ∀ θ ∈ s, |σ' θ| ≤ S')
    (h₁ : ∀ θ ∈ s, |g₁ θ| ≤ κ₁) (h₂ : ∀ θ ∈ s, |g₂ θ| ≤ κ₂)
    (h₁' : ∀ θ ∈ s, |g₁' θ| ≤ κ₁') (h₂' : ∀ θ ∈ s, |g₂' θ| ≤ κ₂') (p : List Bool) :
    (∀ θ ∈ s, |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g₁ θ
        + σ θ * pathWeight g₁ g₂ p θ * g₁' θ|
      ≤ (1 + grow0 κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) / S') * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)
        * (S' * |g₁ θ| + |g₁' θ|)) ∧
    (∀ θ ∈ s, |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g₂ θ
        + σ θ * pathWeight g₁ g₂ p θ * g₂' θ|
      ≤ (1 + grow0 κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) / S') * (κ₁ ^ ktrue p * κ₂ ^ lfalse p)
        * (S' * |g₂ θ| + |g₂' θ|)) := by
  obtain ⟨hA, hB, -, -⟩ := node_weight_bounds hκ₁ hκ₂ hκ₁' hκ₂' hS'.le hσ1 hσ' h₁ h₂ h₁' h₂' p
  have hK : 0 ≤ κ₁ ^ ktrue p * κ₂ ^ lfalse p := by positivity
  have hG0 : 0 ≤ grow0 κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) := by unfold grow0; positivity
  have hgr : growth S' κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) = S' + grow0 κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) := by
    unfold growth grow0; ring
  set G := grow0 κ₁ κ₂ κ₁' κ₂' (lfalse p) (ktrue p) with hG
  set Kp := κ₁ ^ ktrue p * κ₂ ^ lfalse p with hKp
  have key : ∀ (g g' : ℝ) (θ : ℝ), θ ∈ s →
      |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g + σ θ * pathWeight g₁ g₂ p θ * g'|
        ≤ (1 + G / S') * Kp * (S' * |g| + |g'|) := by
    intro g g' θ hθ
    have h1 : |(σ' θ * pathWeight g₁ g₂ p θ + σ θ * pathWeight' g₁ g₂ g₁' g₂' p θ) * g| ≤ (S' + G) * Kp * |g| := by
      rw [abs_mul]; rw [hgr] at hB; exact mul_le_mul_of_nonneg_right (hB θ hθ) (abs_nonneg _)
    have h2 : |σ θ * pathWeight g₁ g₂ p θ * g'| ≤ Kp * |g'| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hA θ hθ) (abs_nonneg _)
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add h1 h2) ?_)
    have e : (1 + G / S') * Kp * (S' * |g| + |g'|) = (S' + G) * Kp * |g| + Kp * |g'| + G / S' * Kp * |g'| := by
      field_simp
      ring
    have : 0 ≤ G / S' * Kp * |g'| := by positivity
    linarith
  exact ⟨fun θ hθ => key (g₁ θ) (g₁' θ) θ hθ, fun θ hθ => key (g₂ θ) (g₂' θ) θ hθ⟩

/-- **The squared coefficient through a pointwise constant**: `|w| ≤ D K B`, `0 ≤ P` and `B² P ≤ C` give
`w² P ≤ (D K)² C`. -/
theorem sq_mul_le_of_abs_le_prod {w D K B P C : ℝ} (hw : |w| ≤ D * K * B) (hDK : 0 ≤ D * K) (hP : 0 ≤ P)
    (hC : B ^ 2 * P ≤ C) : w ^ 2 * P ≤ (D * K) ^ 2 * C := by
  have h1 : w ^ 2 ≤ (D * K * B) ^ 2 := by
    rw [← sq_abs w]; exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  have h2 : w ^ 2 * P ≤ (D * K) ^ 2 * (B ^ 2 * P) := by
    have := mul_le_mul_of_nonneg_right h1 hP
    linarith [show (D * K * B) ^ 2 * P = (D * K) ^ 2 * (B ^ 2 * P) by ring]
  exact h2.trans (mul_le_mul_of_nonneg_left hC (sq_nonneg _))

end Cvs.L2a.HierarchyNodeWeight
