import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# SPINE-L1: the window form on the deep span from above

`QW(k_G) = W_∞(Φ) − 2εW_∞(Φ, Ψ) + ε²W_∞(Ψ)` (Cvs.L2a.WindowFormTailLimit) with `|ε| ≤ ε̄√N`, `|W_∞(Φ, Ψ)| ≤ w̄₁√N` and `|W_∞(Ψ)| ≤ W̄_Ψ`
(the inputs of Cvs.L2a.WindowFormDeepSpan) and `L1FullTailWinfBound`'s `W_∞(Φ) ≤ B̄N` at JA's floor `κ_F` give `QW(k_G) ≤ (B̄ + K_pol(κ_F))·N`, the upper
companion of `WindowFormDeepSpan`'s `b′N ≤ QW(k_G)`.
-/

namespace Cvs.L2a.L1SpineDeepSpanUpper

open Real Set MeasureTheory Filter

/-- **The polar form from above**: `W − 2xB + x²W_Ψ ≤ W + (2we + W̄e²)N` for `|x| ≤ e√N`, `|B| ≤ w√N`, `|W_Ψ| ≤ W̄`. -/
theorem polar_upper {W B WΨ x e w WB N : ℝ} (hN : 0 ≤ N) (hx : |x| ≤ e * √N) (hB : |B| ≤ w * √N)
    (hΨ : |WΨ| ≤ WB) (he : 0 ≤ e) :
    W - 2 * x * B + x ^ 2 * WΨ ≤ W + (2 * w * e + WB * e ^ 2) * N := by
  have hsN : √N * √N = N := Real.mul_self_sqrt hN
  have hxB : -(x * B) ≤ e * w * N := by
    calc -(x * B) ≤ |x * B| := neg_le_abs _
      _ = |x| * |B| := abs_mul _ _
      _ ≤ (e * √N) * (w * √N) := mul_le_mul hx hB (abs_nonneg _) (by positivity)
      _ = e * w * (√N * √N) := by ring
      _ = e * w * N := by rw [hsN]
  have hx2 : x ^ 2 ≤ e ^ 2 * N := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (e * √N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      _ = e ^ 2 * N := by rw [mul_pow, Real.sq_sqrt hN]
  have hWB0 : 0 ≤ WB := (abs_nonneg _).trans hΨ
  have h1 : x ^ 2 * WΨ ≤ x ^ 2 * WB := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hΨ) (sq_nonneg _)
  have h2 : x ^ 2 * WB ≤ e ^ 2 * N * WB := mul_le_mul_of_nonneg_right hx2 hWB0
  nlinarith

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end Cvs.L2a.L1SpineDeepSpanUpper
