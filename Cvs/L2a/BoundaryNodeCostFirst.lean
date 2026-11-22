import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.BoundaryFreeNodeCostFirst
import Cvs.L2a.FluxTermNormVNorm
import Cvs.L2a.HierarchyFirstPairNodeInterval
import Cvs.L2a.HierarchyModePairFactors
import Cvs.L2a.HierarchyModePairNode

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cost of a node with its boundary at `R`, pairs `(1, k)`

On `[L, R]`, `4/3 ≤ L`, for the pair `(1, k)`, `t = k² ≥ 4`, with a weight `σ` vanishing at `L` only and the sources `r₁ = f₁⁺`, `r₂ = t f₂⁺`:
`|∫ σ f₁f₂| ≤ |σ(R)(g₁ f₁u₂ − g₂ u₁f₂)(R)| + (λ₁C₁/2)∫ f₁² + (1/2λ₁)∫ u₂²/P₂ + (λ₂C₂/2)∫ f₂² + (1/2λ₂)∫ u₁²/P₁ + t|∫ σg₁ f₁f₂⁺| + |∫ σg₂ f₁⁺f₂|`
with `P_i = p_i q̄_i` the centred products, `C₁ ≥ (σ'g₁ + σg₁')²P₂`, `C₂ ≥ (σ'g₂ + σg₂')²P₁` on `[L, R]`: the node
(Cvs.L2a.HierarchyFirstPairNodeInterval) with its boundary term at `R`, its `f u` terms by Cvs.L2a.FluxTermNormVNorm and its source term as the two children (Cvs.L2a.BoundaryFreeNodeCostFirst).
-/

namespace Cvs.L2a.BoundaryNodeCostFirst

open Real Set intervalIntegral Cvs.L2a.HierarchyModePairFactors Cvs.L2a.HierarchyModePairNode Cvs.L2a.HierarchyFirstPairNodeInterval Cvs.L2a.BoundaryFreeNodeCostFirst

/-- **The cost of a node with its boundary at `R`**, pairs `(1, k)`. -/
theorem node_cost_first_bd {c t L R χb lam₁ lam₂ C₁ C₂ : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hL : 4 / 3 ≤ L)
    (hLR : L ≤ R) (hχ : χb < c ^ 2 * 1 * L ^ 2) (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂)
    {σ σ' f₁ u₁ f₁p f₂ u₂ f₂p : ℝ → ℝ}
    (hσ : ∀ θ ∈ Icc L R, HasDerivAt σ (σ' θ) θ) (hσ'c : ContinuousOn σ' (Icc L R)) (hσL : σ L = 0)
    (hf₁ : ∀ θ ∈ Icc L R, HasDerivAt f₁ (u₁ θ / (1 * θ ^ 2 - 1)) θ)
    (hu₁ : ∀ θ ∈ Icc L R, HasDerivAt u₁ (-(c ^ 2 * 1 ^ 2 * θ ^ 2 * f₁ θ) + 1 * f₁p θ) θ)
    (hf₂ : ∀ θ ∈ Icc L R, HasDerivAt f₂ (u₂ θ / (t * θ ^ 2 - 1)) θ)
    (hu₂ : ∀ θ ∈ Icc L R, HasDerivAt u₂ (-(c ^ 2 * t ^ 2 * θ ^ 2 * f₂ θ) + t * f₂p θ) θ)
    (hf₁p : ContinuousOn f₁p (Icc L R)) (hf₂p : ContinuousOn f₂p (Icc L R))
    (hC₁ : ∀ θ ∈ Icc L R, (σ' θ * g₁ c 1 t θ + σ θ * g₁' c 1 t θ) ^ 2
      * ((t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb)) ≤ C₁)
    (hC₂ : ∀ θ ∈ Icc L R, (σ' θ * g₂ c 1 t θ + σ θ * g₂' c 1 t θ) ^ 2
      * ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb)) ≤ C₂) :
    |∫ θ in L..R, σ θ * (f₁ θ * f₂ θ)|
      ≤ |σ R * g₁ c 1 t R * (f₁ R * u₂ R) - σ R * g₂ c 1 t R * (u₁ R * f₂ R)|
        + lam₁ * C₁ / 2 * (∫ θ in L..R, f₁ θ ^ 2)
          + 1 / (2 * lam₁) * (∫ θ in L..R, u₂ θ ^ 2 / ((t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb)))
        + (lam₂ * C₂ / 2 * (∫ θ in L..R, f₂ θ ^ 2)
          + 1 / (2 * lam₂) * (∫ θ in L..R, u₁ θ ^ 2 / ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb))))
        + (t * |∫ θ in L..R, σ θ * g₁ c 1 t θ * (f₁ θ * f₂p θ)|
          + 1 * |∫ θ in L..R, σ θ * g₂ c 1 t θ * (f₁p θ * f₂ θ)|) := by
  have hθL : ∀ θ ∈ Icc L R, 4 / 3 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hL0 : 0 < L := by linarith
  have hσc : ContinuousOn σ (Icc L R) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
  have hf₁c : ContinuousOn f₁ (Icc L R) := fun θ hθ => (hf₁ θ hθ).continuousAt.continuousWithinAt
  have hu₁c : ContinuousOn u₁ (Icc L R) := fun θ hθ => (hu₁ θ hθ).continuousAt.continuousWithinAt
  have hf₂c : ContinuousOn f₂ (Icc L R) := fun θ hθ => (hf₂ θ hθ).continuousAt.continuousWithinAt
  have hu₂c : ContinuousOn u₂ (Icc L R) := fun θ hθ => (hu₂ θ hθ).continuousAt.continuousWithinAt
  obtain ⟨hg₁c, hg₂c, hg₁'c, hg₂'c⟩ := continuousOn_factors_first (R := R) hc ht hL
  have hαc : ContinuousOn (fun θ => σ' θ * g₁ c 1 t θ + σ θ * g₁' c 1 t θ) (Icc L R) :=
    (hσ'c.mul hg₁c).add (hσc.mul hg₁'c)
  have hβc : ContinuousOn (fun θ => σ' θ * g₂ c 1 t θ + σ θ * g₂' c 1 t θ) (Icc L R) :=
    (hσ'c.mul hg₂c).add (hσc.mul hg₂'c)
  -- the centred products are positive
  have hP₁ : ∀ θ ∈ Icc L R, 0 < (1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 16 / 9 ≤ θ ^ 2 := by nlinarith [hθL θ hθ]
    have h1 : 0 < 1 * θ ^ 2 - 1 := by nlinarith
    have h2 : c ^ 2 * 1 * L ^ 2 ≤ c ^ 2 * 1 * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hθ2 (mul_nonneg (sq_nonneg c) (by norm_num))
    have h3 : 0 < c ^ 2 * 1 * θ ^ 2 - χb := by linarith
    have : 0 < 1 * (c ^ 2 * 1 * θ ^ 2 - χb) := mul_pos (by norm_num) h3
    exact mul_pos h1 (by nlinarith)
  have hP₂ : ∀ θ ∈ Icc L R, 0 < (t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 16 / 9 ≤ θ ^ 2 := by nlinarith [hθL θ hθ]
    have h1 : 0 < t * θ ^ 2 - 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ2' (by linarith : (0:ℝ) ≤ t)]
    have h2 : c ^ 2 * 1 * L ^ 2 ≤ c ^ 2 * t * θ ^ 2 := by
      have hc2L : 0 ≤ c ^ 2 * L ^ 2 := by positivity
      have : c ^ 2 * 1 * L ^ 2 ≤ c ^ 2 * t * L ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ t) hc2L]
      have : c ^ 2 * t * L ^ 2 ≤ c ^ 2 * t * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hθ2 (mul_nonneg (sq_nonneg c) (by linarith))
      linarith
    have h3 : 0 < c ^ 2 * t * θ ^ 2 - χb := by linarith
    have : 0 < t * (c ^ 2 * t * θ ^ 2 - χb) := mul_pos (by linarith) h3
    exact mul_pos h1 (by nlinarith)
  -- the node
  have hnode := node_abs_le_first' hc ht hL hLR hσ hσ'c hf₁ hu₁ hf₂ hu₂
    (r₁ := fun θ => 1 * f₁p θ) (r₂ := fun θ => t * f₂p θ) (continuousOn_const.mul hf₁p) (continuousOn_const.mul hf₂p)
  rw [hσL] at hnode
  simp only [zero_mul, sub_zero] at hnode
  -- the `f u` terms
  have hA := Cvs.L2a.FluxTermNormVNorm.fu_term_le_sup (P := fun θ => (t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb))
    hLR hl₁ hP₂ hC₁ hαc hf₁c hu₂c (by fun_prop)
  have hB := Cvs.L2a.FluxTermNormVNorm.fu_term_le_sup (P := fun θ => (1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb))
    hLR hl₂ hP₁ hC₂ hβc hf₂c hu₁c (by fun_prop)
  have eβ : (fun θ => (σ' θ * g₂ c 1 t θ + σ θ * g₂' c 1 t θ) * (u₁ θ * f₂ θ))
      = fun θ => (σ' θ * g₂ c 1 t θ + σ θ * g₂' c 1 t θ) * (f₂ θ * u₁ θ) := by funext θ; ring
  rw [eβ] at hnode
  -- the source term
  have hS := source_le_children_first hc ht hL hLR hσc hf₁c hf₂c hf₁p hf₂p
  linarith [hnode, hA, hB, hS]

end Cvs.L2a.BoundaryNodeCostFirst
