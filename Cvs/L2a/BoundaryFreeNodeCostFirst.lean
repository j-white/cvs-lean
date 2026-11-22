import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
# The cost of a boundary-free node, pairs `(1, k)`

On `[L, R]`, `4/3 ≤ L`, for the pair `(1, k)`, `t = k² ≥ 4`, with a weight `σ` vanishing at `L` and `R` and the sources `r₁ = f₁⁺`, `r₂ = t f₂⁺`:
`|∫ σ f₁f₂| ≤ (λ₁C₁/2)∫ f₁² + (1/2λ₁)∫ u₂²/P₂ + (λ₂C₂/2)∫ f₂² + (1/2λ₂)∫ u₁²/P₁ + t|∫ σg₁ f₁f₂⁺| + |∫ σg₂ f₁⁺f₂|`
with `P_i = p_i q̄_i` the centred products, `C₁ ≥ (σ'g₁ + σg₁')²P₂`, `C₂ ≥ (σ'g₂ + σg₂')²P₁` on `[L, R]`: the node
(Cvs.L2a.HierarchyFirstPairNodeInterval) with its `f u` terms by Cvs.L2a.FluxTermNormVNorm and its source term as the two children (an earlier result on `[L, R]`).
-/

namespace Cvs.L2a.BoundaryFreeNodeCostFirst

open Real Set intervalIntegral Cvs.L2a.HierarchyModePairFactors Cvs.L2a.HierarchyModePairNode Cvs.L2a.HierarchyFirstPairNodeInterval

/-- The factors of `(1, k)` and their derivatives are continuous on `[L, R]`, `4/3 ≤ L`. -/
theorem continuousOn_factors_first {c t L R : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hL : 4 / 3 ≤ L) :
    ContinuousOn (g₁ c 1 t) (Icc L R) ∧ ContinuousOn (g₂ c 1 t) (Icc L R) ∧
    ContinuousOn (g₁' c 1 t) (Icc L R) ∧ ContinuousOn (g₂' c 1 t) (Icc L R) := by
  have hθL : ∀ θ ∈ Icc L R, 4 / 3 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hden : ∀ θ ∈ Icc L R, c ^ 2 * (t - 1) * θ ^ 4 * (t + 1 - 1 * t * θ ^ 2) ^ 2 ≠ 0 := fun θ hθ => by
    have hts : 0 < t - 1 := by linarith
    have hθ0 : 0 < θ := by linarith [hθL θ hθ]
    have hq : t + 1 - 1 * t * θ ^ 2 ≠ 0 := by linarith [tθ_pos_first ht (hθL θ hθ)]
    exact (mul_pos (mul_pos (mul_pos (by positivity) hts) (by positivity)) (by positivity)).ne'
  refine ⟨fun θ hθ => (hasDerivAt_g₁_first' hc ht (hθL θ hθ)).continuousAt.continuousWithinAt,
    fun θ hθ => (hasDerivAt_g₂_first' hc ht (hθL θ hθ)).continuousAt.continuousWithinAt, ?_, ?_⟩
  · unfold g₁'
    exact ContinuousOn.div (Continuous.continuousOn (by continuity))
      (Continuous.continuousOn (by continuity)) hden
  · unfold g₂'
    exact ContinuousOn.div (Continuous.continuousOn (by continuity))
      (Continuous.continuousOn (by continuity)) hden

/-- **The source term is the two children**, pair `(1, k)` on `[L, R]`. -/
theorem source_le_children_first {c t L R : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hL : 4 / 3 ≤ L)
    (hLR : L ≤ R) {σ f₁ f₁p f₂ f₂p : ℝ → ℝ}
    (hσc : ContinuousOn σ (Icc L R)) (hf₁ : ContinuousOn f₁ (Icc L R)) (hf₂ : ContinuousOn f₂ (Icc L R))
    (hf₁p : ContinuousOn f₁p (Icc L R)) (hf₂p : ContinuousOn f₂p (Icc L R)) :
    |∫ θ in L..R, σ θ / D0 c 1 t θ
        * ((1 * θ ^ 2 - 1) * f₁ θ * (t * f₂p θ) - (t * θ ^ 2 - 1) * (1 * f₁p θ) * f₂ θ)|
      ≤ t * |∫ θ in L..R, σ θ * g₁ c 1 t θ * (f₁ θ * f₂p θ)|
        + 1 * |∫ θ in L..R, σ θ * g₂ c 1 t θ * (f₁p θ * f₂ θ)| := by
  obtain ⟨hg₁c, hg₂c, -, -⟩ := continuousOn_factors_first (R := R) hc ht hL
  have e : (fun θ => σ θ / D0 c 1 t θ
      * ((1 * θ ^ 2 - 1) * f₁ θ * (t * f₂p θ) - (t * θ ^ 2 - 1) * (1 * f₁p θ) * f₂ θ))
      = fun θ => t * (σ θ * g₁ c 1 t θ * (f₁ θ * f₂p θ)) - 1 * (σ θ * g₂ c 1 t θ * (f₁p θ * f₂ θ)) := by
    funext θ; unfold g₁ g₂; ring
  rw [e]
  have h1 : IntervalIntegrable (fun θ => σ θ * g₁ c 1 t θ * (f₁ θ * f₂p θ)) MeasureTheory.volume L R :=
    ((hσc.mul hg₁c).mul (hf₁.mul hf₂p)).intervalIntegrable_of_Icc hLR
  have h2 : IntervalIntegrable (fun θ => σ θ * g₂ c 1 t θ * (f₁p θ * f₂ θ)) MeasureTheory.volume L R :=
    ((hσc.mul hg₂c).mul (hf₁p.mul hf₂)).intervalIntegrable_of_Icc hLR
  rw [integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
  have hs0 : (0:ℝ) ≤ 1 := by norm_num
  have ht0 : 0 ≤ t := by linarith
  calc |(t * ∫ θ in L..R, σ θ * g₁ c 1 t θ * (f₁ θ * f₂p θ))
        - 1 * ∫ θ in L..R, σ θ * g₂ c 1 t θ * (f₁p θ * f₂ θ)|
      ≤ |t * ∫ θ in L..R, σ θ * g₁ c 1 t θ * (f₁ θ * f₂p θ)|
        + |1 * ∫ θ in L..R, σ θ * g₂ c 1 t θ * (f₁p θ * f₂ θ)| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hs0]

end Cvs.L2a.BoundaryFreeNodeCostFirst
