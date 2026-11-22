import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.PositionTruncatedTail

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A bound on every position truncation bounds the full tail

For a `C²` profile `g`, if `∫_{θ>1} F_X² ≤ K` for every `X ≥ 1` then `∫_{θ>1} F_∞² ≤ K`: pointwise
`(x + y)² ≤ (1 + ε)x² + (1 + 1/ε)y²` with `y = F_∞ − F_X`, `FullTailConvergence`'s rate `‖F_X − F_∞‖² ≤ K1b/√X`, then `X → ∞` and
`ε → 0`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.L2a.PositionToFullTailBound

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.FullTailConvergence (fullTail)

/-- **The full tail inherits a uniform bound on the truncations.** -/
theorem integral_fullTail_sq_le {g g₁ g₂ : ℝ → ℝ} {c K : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c)
    (hK : ∀ X : ℝ, 1 ≤ X → ∫ θ in Ioi 1, posTail (psi c g) X θ ^ 2 ≤ K) :
    ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2 ≤ K := by
  set F := fullTail (psi c g)
  set Kb := Cvs.L2a.FullTailConvergence.K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) with hKb
  have hτ := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc
  have hF2 : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1) :=
    Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hτ fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hψc : Continuous (psi c g) := (Cvs.L2a.FullTailConvergence.contDiff_psi hgc c).continuous
  -- for every `ε > 0` and `X ≥ 1`
  have key : ∀ ε : ℝ, 0 < ε → ∀ X : ℝ, 1 ≤ X →
      ∫ θ in Ioi 1, F θ ^ 2 ≤ (1 + ε) * K + (1 + 1 / ε) * (Kb / √X) := fun ε hε X hX => by
    have hX2 := Cvs.L2a.PositionTruncatedTail.integrableOn_posTail_sq (psi c g) (X := X) hψc.continuousOn
    have hD : IntegrableOn (fun θ => (posTail (psi c g) X θ - F θ) ^ 2) (Ioi 1) :=
      Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le ((Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c X).sub hτ)
        fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc X hθ
    have hgap := (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hg hg₁ hg₂c hc hX).trans
      (Cvs.L2a.FullTailConvergence.K1_le hc _ _ hX)
    have hpt : ∀ θ ∈ Ioi (1 : ℝ), F θ ^ 2
        ≤ (1 + ε) * posTail (psi c g) X θ ^ 2 + (1 + 1 / ε) * (posTail (psi c g) X θ - F θ) ^ 2 := fun θ _ => by
      have h : 0 ≤ (ε * posTail (psi c g) X θ + (posTail (psi c g) X θ - F θ)) ^ 2 / ε := by positivity
      have e : (1 + ε) * posTail (psi c g) X θ ^ 2 + (1 + 1 / ε) * (posTail (psi c g) X θ - F θ) ^ 2 - F θ ^ 2
          = (ε * posTail (psi c g) X θ + (posTail (psi c g) X θ - F θ)) ^ 2 / ε := by
        field_simp; ring
      linarith
    have hint := setIntegral_mono_on hF2 ((hX2.const_mul (1 + ε)).add (hD.const_mul (1 + 1 / ε))) measurableSet_Ioi hpt
    simp only [Pi.add_apply] at hint
    rw [integral_add (hX2.const_mul _) (hD.const_mul _), integral_const_mul, integral_const_mul] at hint
    have h1 := mul_le_mul_of_nonneg_left (hK X hX) (by linarith : (0 : ℝ) ≤ 1 + ε)
    have h2 := mul_le_mul_of_nonneg_left hgap (by positivity : (0 : ℝ) ≤ 1 + 1 / ε)
    linarith
  -- let `X → ∞`, then `ε → 0`
  have hlimX : ∀ ε : ℝ, 0 < ε → ∫ θ in Ioi 1, F θ ^ 2 ≤ (1 + ε) * K := fun ε hε => by
    have ht : Tendsto (fun X : ℝ => (1 + ε) * K + (1 + 1 / ε) * (Kb / √X)) atTop (nhds ((1 + ε) * K)) := by
      have h0 : Tendsto (fun X : ℝ => Kb / √X) atTop (nhds 0) :=
        (tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop))
      simpa using tendsto_const_nhds.add (h0.const_mul (1 + 1 / ε))
    exact ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun X hX => key ε hε X hX⟩)
  have hlimε : Tendsto (fun ε : ℝ => (1 + ε) * K) (nhdsWithin 0 (Ioi 0)) (nhds K) := by
    have : Tendsto (fun ε : ℝ => (1 + ε) * K) (nhds 0) (nhds ((1 + 0) * K)) :=
      ((tendsto_const_nhds.add tendsto_id).mul tendsto_const_nhds)
    simpa using this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlimε (eventually_nhdsWithin_of_forall fun ε hε => hlimX ε hε)

end Cvs.L2a.PositionToFullTailBound
