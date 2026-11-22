import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.WeightedDerivativeNormAbsorbed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The absorbed weighted derivative norm with a majorant of `w'²p/w`

For `w ≥ 0` (vanishing at the ends allowed) and a continuous `W₂ ≥ 0` with `w'²p ≤ W₂ w` pointwise,
`(1 − ε/2)∫ wU²/p ≤ [wGU] + (1/2ε)∫ W₂ G² + ∫ w(qG² − GR)` for every `ε > 0`, by
`2|w'GU| ≤ W₂G²/ε + εwU²/p` from `(w'GU)² ≤ (W₂G²/ε)(εwU²/p)`: the form of an earlier result that a bump weight vanishing at
its ends can use, with no division by `w`.
-/

namespace Cvs.L2a.WeightedDerivativeMajorant

open Real Set intervalIntegral

/-- **Pointwise absorption with a majorant**: for `p > 0`, `w, W₂ ≥ 0`, `w'²p ≤ W₂w` and `ε > 0`,
`−w'GU ≤ (1/2ε) W₂G² + (ε/2) wU²/p`. -/
theorem neg_mul_le_of_maj {w w' W₂ p G U ε : ℝ} (hε : 0 < ε) (hp : 0 < p) (hw : 0 ≤ w) (hW : 0 ≤ W₂)
    (hmaj : w' ^ 2 * p ≤ W₂ * w) :
    -(w' * (G * U)) ≤ 1 / (2 * ε) * (W₂ * G ^ 2) + ε / 2 * (w * (U ^ 2 / p)) := by
  have h1 : w' ^ 2 ≤ W₂ * w / p := by rw [le_div_iff₀ hp]; exact hmaj
  set a := W₂ * G ^ 2 / ε with ha
  set b := ε * (w * (U ^ 2 / p)) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hab : a * b = W₂ * w / p * (G ^ 2 * U ^ 2) := by
    rw [ha, hb]; field_simp
  have hsq : (2 * (w' * (G * U))) ^ 2 ≤ (a + b) ^ 2 := by
    have h2 : w' ^ 2 * (G ^ 2 * U ^ 2) ≤ W₂ * w / p * (G ^ 2 * U ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith [sq_nonneg (a - b)]
  have := (abs_le_of_sq_le_sq' hsq (by positivity)).1
  have e : 1 / (2 * ε) * (W₂ * G ^ 2) + ε / 2 * (w * (U ^ 2 / p)) = (a + b) / 2 := by
    rw [ha, hb]; field_simp
  rw [e]; linarith

/-- **The absorbed norm with a majorant**: `(1 − ε/2)∫ wU²/p ≤ w(β)G(β)U(β) − w(α)G(α)U(α) + (1/2ε)∫ W₂G² + ∫ w(qG² − GR)`. -/
theorem integral_w_u_sq_div_p_le_maj {G U p q R w w' W₂ : ℝ → ℝ} {α β ε : ℝ} (hαβ : α ≤ β) (hε : 0 < ε)
    (hp : ∀ θ ∈ Icc α β, 0 < p θ) (hw0 : ∀ θ ∈ Icc α β, 0 ≤ w θ) (hW : ∀ θ ∈ Icc α β, 0 ≤ W₂ θ)
    (hmaj : ∀ θ ∈ Icc α β, w' θ ^ 2 * p θ ≤ W₂ θ * w θ)
    (hG : ∀ θ ∈ Icc α β, HasDerivAt G (U θ / p θ) θ)
    (hU : ∀ θ ∈ Icc α β, HasDerivAt U (-(q θ * G θ) + R θ) θ)
    (hw : ∀ θ ∈ Icc α β, HasDerivAt w (w' θ) θ) (hw'c : ContinuousOn w' (Icc α β)) (hWc : ContinuousOn W₂ (Icc α β))
    (hpc : ContinuousOn p (Icc α β)) (hqc : ContinuousOn q (Icc α β)) (hRc : ContinuousOn R (Icc α β)) :
    (1 - ε / 2) * ∫ θ in α..β, w θ * (U θ ^ 2 / p θ)
      ≤ (w β * (G β * U β) - w α * (G α * U α)) + 1 / (2 * ε) * (∫ θ in α..β, W₂ θ * G θ ^ 2)
        + ∫ θ in α..β, w θ * (q θ * G θ ^ 2 - G θ * R θ) := by
  have hGc : ContinuousOn G (Icc α β) := fun θ hθ => (hG θ hθ).continuousAt.continuousWithinAt
  have hUc : ContinuousOn U (Icc α β) := fun θ hθ => (hU θ hθ).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Icc α β) := fun θ hθ => (hw θ hθ).continuousAt.continuousWithinAt
  have hid := Cvs.L2a.WeightedDerivativeNormAbsorbed.integral_w_u_sq_div_p hαβ (fun θ hθ => (hp θ hθ).ne') hG hU hw hw'c hpc hqc hRc
  have hpt : ∀ θ ∈ Icc α β, -(w' θ * (G θ * U θ))
      ≤ 1 / (2 * ε) * (W₂ θ * G θ ^ 2) + ε / 2 * (w θ * (U θ ^ 2 / p θ)) := fun θ hθ =>
    neg_mul_le_of_maj hε (hp θ hθ) (hw0 θ hθ) (hW θ hθ) (hmaj θ hθ)
  have h1 : IntervalIntegrable (fun θ => w θ * (U θ ^ 2 / p θ)) MeasureTheory.volume α β :=
    (hwc.mul ((hUc.pow 2).div hpc fun θ hθ => (hp θ hθ).ne')).intervalIntegrable_of_Icc hαβ
  have h2 : IntervalIntegrable (fun θ => w' θ * (G θ * U θ)) MeasureTheory.volume α β :=
    (hw'c.mul (hGc.mul hUc)).intervalIntegrable_of_Icc hαβ
  have h4 : IntervalIntegrable (fun θ => W₂ θ * G θ ^ 2) MeasureTheory.volume α β :=
    (hWc.mul (hGc.pow 2)).intervalIntegrable_of_Icc hαβ
  have h2n : IntervalIntegrable (fun θ => -(w' θ * (G θ * U θ))) MeasureTheory.volume α β := h2.neg
  have hint := integral_mono_on hαβ h2n ((h4.const_mul _).add (h1.const_mul _)) hpt
  rw [integral_neg, integral_add (h4.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul] at hint
  linarith

end Cvs.L2a.WeightedDerivativeMajorant
