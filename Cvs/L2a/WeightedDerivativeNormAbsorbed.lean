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
# The weighted derivative norm of a combination, absorbed

For `G' = U/p`, `U' = −qG + R` and a weight `w > 0` with derivative `w'` on `[α, β]`, `p > 0`,
`∫ w U²/p = [wGU] − ∫ w'GU + ∫ w(qG² − GR)`, and `|w'GU| ≤ (w'²p/(2w))G² + (w/(2p))U²` absorbs half of the left
side: `∫ w U²/p ≤ 2[wGU]_α^β + ∫ (w'²p/w) G² + 2∫ w(qG² − GR)`. The weight is free, so `w = θ^{−4}`
matches the growth of `U ~ cθ²G` in the cross terms of the tail.
-/

namespace Cvs.L2a.WeightedDerivativeNormAbsorbed

open Real Set intervalIntegral

/-- **The weighted derivative norm**: `∫ w U²/p = w(β)G(β)U(β) − w(α)G(α)U(α) − ∫ w'GU + ∫ w(qG² − GR)`. -/
theorem integral_w_u_sq_div_p {G U p q R w w' : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hp : ∀ θ ∈ Icc α β, p θ ≠ 0)
    (hG : ∀ θ ∈ Icc α β, HasDerivAt G (U θ / p θ) θ)
    (hU : ∀ θ ∈ Icc α β, HasDerivAt U (-(q θ * G θ) + R θ) θ)
    (hw : ∀ θ ∈ Icc α β, HasDerivAt w (w' θ) θ) (hw'c : ContinuousOn w' (Icc α β))
    (hpc : ContinuousOn p (Icc α β)) (hqc : ContinuousOn q (Icc α β)) (hRc : ContinuousOn R (Icc α β)) :
    ∫ θ in α..β, w θ * (U θ ^ 2 / p θ)
      = w β * (G β * U β) - w α * (G α * U α) - (∫ θ in α..β, w' θ * (G θ * U θ))
        + ∫ θ in α..β, w θ * (q θ * G θ ^ 2 - G θ * R θ) := by
  have hGc : ContinuousOn G (Icc α β) := fun θ hθ => (hG θ hθ).continuousAt.continuousWithinAt
  have hUc : ContinuousOn U (Icc α β) := fun θ hθ => (hU θ hθ).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Icc α β) := fun θ hθ => (hw θ hθ).continuousAt.continuousWithinAt
  have hI : uIcc α β = Icc α β := uIcc_of_le hαβ
  have hderiv : ∀ θ ∈ uIcc α β, HasDerivAt (fun θ => w θ * (G θ * U θ))
      (w θ * (U θ ^ 2 / p θ) + w' θ * (G θ * U θ) - w θ * (q θ * G θ ^ 2 - G θ * R θ)) θ := fun θ hθ => by
    rw [hI] at hθ
    refine ((hw θ hθ).fun_mul ((hG θ hθ).fun_mul (hU θ hθ))).congr_deriv ?_
    have := hp θ hθ; field_simp; ring
  have h1 : IntervalIntegrable (fun θ => w θ * (U θ ^ 2 / p θ)) MeasureTheory.volume α β :=
    (hwc.mul ((hUc.pow 2).div hpc hp)).intervalIntegrable_of_Icc hαβ
  have h2 : IntervalIntegrable (fun θ => w' θ * (G θ * U θ)) MeasureTheory.volume α β :=
    (hw'c.mul (hGc.mul hUc)).intervalIntegrable_of_Icc hαβ
  have h3 : IntervalIntegrable (fun θ => w θ * (q θ * G θ ^ 2 - G θ * R θ)) MeasureTheory.volume α β :=
    (hwc.mul ((hqc.mul (hGc.pow 2)).sub (hGc.mul hRc))).intervalIntegrable_of_Icc hαβ
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv ((h1.add h2).sub h3)
  rw [integral_sub (h1.add h2) h3, integral_add h1 h2] at hFTC
  linarith

end Cvs.L2a.WeightedDerivativeNormAbsorbed
