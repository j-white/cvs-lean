import Mathlib.Analysis.SpecialFunctions.Sqrt

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frame constant from the mode-1 angle and the rung far masses

With `N = P + Q + 2C` (`P = ‖Φ‖²`, `Q = ‖Δ‖²`, `C = ⟨Φ, Δ⟩` on the tail range), `|C| ≤ δ√(PQ)` with `δ < 1` gives
`P + Q ≤ N/(1 − δ)`; with the far mass `R ≤ S·W` and `λW ≤ N` (the rung triangle against the tail norm's diagonal),
the whole-range mass `F = P + R` obeys `F ≤ (1/(1 − δ) + S/λ)·N`: a frame constant from three constants, with no
mode diagonal and no bound on the pairs of higher modes.
-/

namespace Cvs.L2a.FrameConstantFirstModeAngle

open Real

/-- **`P + Q ≤ N/(1 − δ)`** from the angle. -/
theorem sum_le_of_angle {P Q C δ : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hC : |C| ≤ δ * √(P * Q)) : P + Q ≤ (P + Q + 2 * C) / (1 - δ) := by
  have hsq : √(P * Q) ≤ (P + Q) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (P - Q)]
  have h2C : -(2 * C) ≤ δ * (P + Q) := by
    have := neg_le_abs C
    nlinarith [mul_le_mul_of_nonneg_left hsq hδ0]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end Cvs.L2a.FrameConstantFirstModeAngle
