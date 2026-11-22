import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `ε`-parametric floor through `√N`

With the corner split (Cvs.L2a.DilationCornerSplit) at `θ = 0` and the `e₁` charge through `√N` (Cvs.L2a.DefectChargeSqrtN), `FrameFloorJumpAbsorption`'s floor reads
`N + 2ε√P√N ≥ A·P` with `A = ½ − 3ε − η − (r₁ + r₂ + r₃)`. Solving the quadratic in `√N` gives
`N ≥ (√(A + ε²) − ε)²·P` for `A ≥ 0`, and `FrameFloorJumpAbsorption`'s `FF_of_floor` turns this into the frame floor.
-/

noncomputable section

open MeasureTheory Set Real

namespace Cvs.L2a.ParametricFloorSqrtN

local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

/-! ### The quadratic in `√N` -/

/-- **The linear root bound**: for `x, y, e ≥ 0` with `A y² ≤ x² + 2eyx`, `(√(A + e²) − e) y ≤ x`, for every
real `A` (if `A + e² < 0` the left side is `−ey ≤ 0`). -/
theorem le_of_sq_add_two_mul {x y e A : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e)
    (h : A * y ^ 2 ≤ x ^ 2 + 2 * e * y * x) : (√(A + e ^ 2) - e) * y ≤ x := by
  have hsq : (A + e ^ 2) * y ^ 2 ≤ (x + e * y) ^ 2 := by nlinarith
  have hroot := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul' _ (sq_nonneg y), Real.sqrt_sq hy,
    Real.sqrt_sq (add_nonneg hx (mul_nonneg he hy))] at hroot
  linarith

/-- **The squared root bound**: for `N, P, e ≥ 0`, `A ≥ 0` and `A P ≤ N + 2e√P√N`, `(√(A + e²) − e)² P ≤ N`. -/
theorem sq_le_of_quadratic {N P e A : ℝ} (hN : 0 ≤ N) (hP : 0 ≤ P) (he : 0 ≤ e) (hA : 0 ≤ A)
    (h : A * P ≤ N + 2 * e * (√P * √N)) : (√(A + e ^ 2) - e) ^ 2 * P ≤ N := by
  have hlin := le_of_sq_add_two_mul (Real.sqrt_nonneg N) (Real.sqrt_nonneg P) he
    (A := A) (by rw [Real.sq_sqrt hP, Real.sq_sqrt hN]; linarith)
  have he' : e ≤ √(A + e ^ 2) := by
    calc e = √(e ^ 2) := (Real.sqrt_sq he).symm
      _ ≤ √(A + e ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h0 : 0 ≤ (√(A + e ^ 2) - e) * √P := mul_nonneg (by linarith) (Real.sqrt_nonneg P)
  have h2 := pow_le_pow_left₀ h0 hlin 2
  rwa [mul_pow, Real.sq_sqrt hP, Real.sq_sqrt hN] at h2

/-! ### The floor on the rung span -/

end Cvs.L2a.ParametricFloorSqrtN
