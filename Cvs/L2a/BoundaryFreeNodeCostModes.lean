import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.FluxTermNormVNorm
import Cvs.L2a.HierarchyModePairFactors
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.HierarchyModePairNodeInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cost of a boundary-free node, mode pairs `≥ 2`

On `[L, R]`, `19/20 ≤ L`, with a weight `σ` vanishing at `L` and `R` and the sources `r₁ = s f₁⁺`, `r₂ = t f₂⁺`:
`|∫ σ f₁f₂| ≤ (λ₁C₁/2)∫ f₁² + (1/2λ₁)∫ u₂²/P₂ + (λ₂C₂/2)∫ f₂² + (1/2λ₂)∫ u₁²/P₁ + t|∫ σg₁ f₁f₂⁺| + s|∫ σg₂ f₁⁺f₂|`
with `P_i = p_i q̄_i` the centred products, `C₁ ≥ (σ'g₁ + σg₁')²P₂`, `C₂ ≥ (σ'g₂ + σg₂')²P₁` on `[L, R]`: the node
(Cvs.L2a.HierarchyModePairNodeInterval) with its `f u` terms by Cvs.L2a.FluxTermNormVNorm and its source term as the two children (an earlier result on `[L, R]`).
-/

namespace Cvs.L2a.BoundaryFreeNodeCostModes

open Real Set intervalIntegral Cvs.L2a.HierarchyModePairFactors Cvs.L2a.HierarchyModePairNode Cvs.L2a.HierarchyModePairNodeInterval

/-- The factors and their derivatives are continuous on `[L, R]`, `19/20 ≤ L`. -/
theorem continuousOn_factors {c s t L R : ℝ} (hc : 0 < c) (hs : 4 ≤ s) (hst : s + 5 ≤ t) (hL : 19 / 20 ≤ L) :
    ContinuousOn (g₁ c s t) (Icc L R) ∧ ContinuousOn (g₂ c s t) (Icc L R) ∧
    ContinuousOn (g₁' c s t) (Icc L R) ∧ ContinuousOn (g₂' c s t) (Icc L R) := by
  have hθL : ∀ θ ∈ Icc L R, 19 / 20 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hden : ∀ θ ∈ Icc L R, c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2 ≠ 0 := fun θ hθ => by
    have hts : 0 < t - s := by linarith
    have hθ0 : 0 < θ := by linarith [hθL θ hθ]
    have hq : t + s - s * t * θ ^ 2 ≠ 0 := by linarith [stθ_pos hs hst (hθL θ hθ)]
    exact (mul_pos (mul_pos (mul_pos (by positivity) hts) (by positivity)) (by positivity)).ne'
  refine ⟨fun θ hθ => (hasDerivAt_g₁' hc hs hst (hθL θ hθ)).continuousAt.continuousWithinAt,
    fun θ hθ => (hasDerivAt_g₂' hc hs hst (hθL θ hθ)).continuousAt.continuousWithinAt, ?_, ?_⟩
  · have hn : ContinuousOn (fun θ : ℝ => 2 * θ * (s ^ 2 * t * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s))
        (Icc L R) := by fun_prop
    have hd : ContinuousOn (fun θ : ℝ => c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2)
        (Icc L R) := by fun_prop
    exact hn.div hd hden
  · have hn : ContinuousOn (fun θ : ℝ => 2 * θ * (s * t ^ 2 * θ ^ 4 - 2 * s * t * θ ^ 2 + t + s))
        (Icc L R) := by fun_prop
    have hd : ContinuousOn (fun θ : ℝ => c ^ 2 * (t - s) * θ ^ 4 * (t + s - s * t * θ ^ 2) ^ 2)
        (Icc L R) := by fun_prop
    exact hn.div hd hden

/-- **The source term is the two children**, on `[L, R]` (an earlier result with `19/20 ≤ L`). -/
theorem source_le_children' {c s t L R : ℝ} (hc : 0 < c) (hs : 4 ≤ s) (hst : s + 5 ≤ t) (hL : 19 / 20 ≤ L)
    (hLR : L ≤ R) {σ f₁ f₁p f₂ f₂p : ℝ → ℝ}
    (hσc : ContinuousOn σ (Icc L R)) (hf₁ : ContinuousOn f₁ (Icc L R)) (hf₂ : ContinuousOn f₂ (Icc L R))
    (hf₁p : ContinuousOn f₁p (Icc L R)) (hf₂p : ContinuousOn f₂p (Icc L R)) :
    |∫ θ in L..R, σ θ / D0 c s t θ
        * ((s * θ ^ 2 - 1) * f₁ θ * (t * f₂p θ) - (t * θ ^ 2 - 1) * (s * f₁p θ) * f₂ θ)|
      ≤ t * |∫ θ in L..R, σ θ * g₁ c s t θ * (f₁ θ * f₂p θ)|
        + s * |∫ θ in L..R, σ θ * g₂ c s t θ * (f₁p θ * f₂ θ)| := by
  obtain ⟨hg₁c, hg₂c, -, -⟩ := continuousOn_factors (R := R) hc hs hst hL
  have e : (fun θ => σ θ / D0 c s t θ
      * ((s * θ ^ 2 - 1) * f₁ θ * (t * f₂p θ) - (t * θ ^ 2 - 1) * (s * f₁p θ) * f₂ θ))
      = fun θ => t * (σ θ * g₁ c s t θ * (f₁ θ * f₂p θ)) - s * (σ θ * g₂ c s t θ * (f₁p θ * f₂ θ)) := by
    funext θ; unfold g₁ g₂; ring
  rw [e]
  have h1 : IntervalIntegrable (fun θ => σ θ * g₁ c s t θ * (f₁ θ * f₂p θ)) MeasureTheory.volume L R :=
    ((hσc.mul hg₁c).mul (hf₁.mul hf₂p)).intervalIntegrable_of_Icc hLR
  have h2 : IntervalIntegrable (fun θ => σ θ * g₂ c s t θ * (f₁p θ * f₂ θ)) MeasureTheory.volume L R :=
    ((hσc.mul hg₂c).mul (hf₁p.mul hf₂)).intervalIntegrable_of_Icc hLR
  rw [integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := by linarith
  calc |(t * ∫ θ in L..R, σ θ * g₁ c s t θ * (f₁ θ * f₂p θ))
        - s * ∫ θ in L..R, σ θ * g₂ c s t θ * (f₁p θ * f₂ θ)|
      ≤ |t * ∫ θ in L..R, σ θ * g₁ c s t θ * (f₁ θ * f₂p θ)|
        + |s * ∫ θ in L..R, σ θ * g₂ c s t θ * (f₁p θ * f₂ θ)| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hs0]

/-- **The cost of a boundary-free node**, mode pairs `≥ 2`. -/
theorem node_cost {c s t L R χb lam₁ lam₂ C₁ C₂ : ℝ} (hc : 0 < c) (hs : 4 ≤ s) (hst : s + 5 ≤ t) (hL : 19 / 20 ≤ L)
    (hLR : L ≤ R) (hχ : χb < c ^ 2 * s * L ^ 2) (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂)
    {σ σ' f₁ u₁ f₁p f₂ u₂ f₂p : ℝ → ℝ}
    (hσ : ∀ θ ∈ Icc L R, HasDerivAt σ (σ' θ) θ) (hσ'c : ContinuousOn σ' (Icc L R)) (hσL : σ L = 0) (hσR : σ R = 0)
    (hf₁ : ∀ θ ∈ Icc L R, HasDerivAt f₁ (u₁ θ / (s * θ ^ 2 - 1)) θ)
    (hu₁ : ∀ θ ∈ Icc L R, HasDerivAt u₁ (-(c ^ 2 * s ^ 2 * θ ^ 2 * f₁ θ) + s * f₁p θ) θ)
    (hf₂ : ∀ θ ∈ Icc L R, HasDerivAt f₂ (u₂ θ / (t * θ ^ 2 - 1)) θ)
    (hu₂ : ∀ θ ∈ Icc L R, HasDerivAt u₂ (-(c ^ 2 * t ^ 2 * θ ^ 2 * f₂ θ) + t * f₂p θ) θ)
    (hf₁p : ContinuousOn f₁p (Icc L R)) (hf₂p : ContinuousOn f₂p (Icc L R))
    (hC₁ : ∀ θ ∈ Icc L R, (σ' θ * g₁ c s t θ + σ θ * g₁' c s t θ) ^ 2
      * ((t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb)) ≤ C₁)
    (hC₂ : ∀ θ ∈ Icc L R, (σ' θ * g₂ c s t θ + σ θ * g₂' c s t θ) ^ 2
      * ((s * θ ^ 2 - 1) * (c ^ 2 * s ^ 2 * θ ^ 2 - s * χb)) ≤ C₂) :
    |∫ θ in L..R, σ θ * (f₁ θ * f₂ θ)|
      ≤ lam₁ * C₁ / 2 * (∫ θ in L..R, f₁ θ ^ 2)
          + 1 / (2 * lam₁) * (∫ θ in L..R, u₂ θ ^ 2 / ((t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb)))
        + (lam₂ * C₂ / 2 * (∫ θ in L..R, f₂ θ ^ 2)
          + 1 / (2 * lam₂) * (∫ θ in L..R, u₁ θ ^ 2 / ((s * θ ^ 2 - 1) * (c ^ 2 * s ^ 2 * θ ^ 2 - s * χb))))
        + (t * |∫ θ in L..R, σ θ * g₁ c s t θ * (f₁ θ * f₂p θ)|
          + s * |∫ θ in L..R, σ θ * g₂ c s t θ * (f₁p θ * f₂ θ)|) := by
  have hθL : ∀ θ ∈ Icc L R, 19 / 20 ≤ θ := fun θ hθ => hL.trans hθ.1
  have hL0 : 0 < L := by linarith
  have hσc : ContinuousOn σ (Icc L R) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
  have hf₁c : ContinuousOn f₁ (Icc L R) := fun θ hθ => (hf₁ θ hθ).continuousAt.continuousWithinAt
  have hu₁c : ContinuousOn u₁ (Icc L R) := fun θ hθ => (hu₁ θ hθ).continuousAt.continuousWithinAt
  have hf₂c : ContinuousOn f₂ (Icc L R) := fun θ hθ => (hf₂ θ hθ).continuousAt.continuousWithinAt
  have hu₂c : ContinuousOn u₂ (Icc L R) := fun θ hθ => (hu₂ θ hθ).continuousAt.continuousWithinAt
  obtain ⟨hg₁c, hg₂c, hg₁'c, hg₂'c⟩ := continuousOn_factors (R := R) hc hs hst hL
  have hαc : ContinuousOn (fun θ => σ' θ * g₁ c s t θ + σ θ * g₁' c s t θ) (Icc L R) :=
    (hσ'c.mul hg₁c).add (hσc.mul hg₁'c)
  have hβc : ContinuousOn (fun θ => σ' θ * g₂ c s t θ + σ θ * g₂' c s t θ) (Icc L R) :=
    (hσ'c.mul hg₂c).add (hσc.mul hg₂'c)
  -- the centred products are positive
  have hP₁ : ∀ θ ∈ Icc L R, 0 < (s * θ ^ 2 - 1) * (c ^ 2 * s ^ 2 * θ ^ 2 - s * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 361 / 400 ≤ θ ^ 2 := by nlinarith [hθL θ hθ]
    have h1 : 0 < s * θ ^ 2 - 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ2' (by linarith : (0:ℝ) ≤ s)]
    have h2 : c ^ 2 * s * L ^ 2 ≤ c ^ 2 * s * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hθ2 (mul_nonneg (sq_nonneg c) (by linarith))
    have h3 : 0 < c ^ 2 * s * θ ^ 2 - χb := by linarith
    have : 0 < s * (c ^ 2 * s * θ ^ 2 - χb) := mul_pos (by linarith) h3
    exact mul_pos h1 (by nlinarith)
  have hP₂ : ∀ θ ∈ Icc L R, 0 < (t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb) := fun θ hθ => by
    have hθ2 : L ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hL0.le hθ.1 2
    have hθ2' : 361 / 400 ≤ θ ^ 2 := by nlinarith [hθL θ hθ]
    have h1 : 0 < t * θ ^ 2 - 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ2' (by linarith : (0:ℝ) ≤ t)]
    have h2 : c ^ 2 * s * L ^ 2 ≤ c ^ 2 * t * θ ^ 2 := by
      have hc2L : 0 ≤ c ^ 2 * L ^ 2 := by positivity
      have : c ^ 2 * s * L ^ 2 ≤ c ^ 2 * t * L ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left (by linarith : s ≤ t) hc2L]
      have : c ^ 2 * t * L ^ 2 ≤ c ^ 2 * t * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hθ2 (mul_nonneg (sq_nonneg c) (by linarith))
      linarith
    have h3 : 0 < c ^ 2 * t * θ ^ 2 - χb := by linarith
    have : 0 < t * (c ^ 2 * t * θ ^ 2 - χb) := mul_pos (by linarith) h3
    exact mul_pos h1 (by nlinarith)
  -- the node
  have hnode := node_abs_le_cutoff hc hs hst hL hLR hσ hσ'c hσL hσR hf₁ hu₁ hf₂ hu₂
    (r₁ := fun θ => s * f₁p θ) (r₂ := fun θ => t * f₂p θ) (continuousOn_const.mul hf₁p) (continuousOn_const.mul hf₂p)
  -- the `f u` terms
  have hA := Cvs.L2a.FluxTermNormVNorm.fu_term_le_sup (P := fun θ => (t * θ ^ 2 - 1) * (c ^ 2 * t ^ 2 * θ ^ 2 - t * χb))
    hLR hl₁ hP₂ hC₁ hαc hf₁c hu₂c (by fun_prop)
  have hB := Cvs.L2a.FluxTermNormVNorm.fu_term_le_sup (P := fun θ => (s * θ ^ 2 - 1) * (c ^ 2 * s ^ 2 * θ ^ 2 - s * χb))
    hLR hl₂ hP₁ hC₂ hβc hf₂c hu₁c (by fun_prop)
  have eβ : (fun θ => (σ' θ * g₂ c s t θ + σ θ * g₂' c s t θ) * (u₁ θ * f₂ θ))
      = fun θ => (σ' θ * g₂ c s t θ + σ θ * g₂' c s t θ) * (f₂ θ * u₁ θ) := by funext θ; ring
  rw [eβ] at hnode
  -- the source term
  have hS := source_le_children' hc hs hst hL hLR hσc hf₁c hf₂c hf₁p hf₂p
  linarith [hnode, hA, hB, hS]

end Cvs.L2a.BoundaryFreeNodeCostModes
