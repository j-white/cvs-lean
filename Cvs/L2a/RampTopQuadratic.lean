import Mathlib
import Cvs.L2a.ChebyshevRampBound
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The top of the ramp: `1 − wF` vanishes quadratically at `2`

On `[3/2, 2]`, `1 − wF(x) = sin²(π(2 − x))`, so `1 − wF(x) ≤ π²(2 − x)²` for every real `x`.
At `x = 2z` with `z ≥ 0` and `ζ = 1 − z²` this gives the near weight `1 − wF(2z) ≤ (64π²/49)ζ²`.
-/

noncomputable section

open Real Set Cvs.L2a.FarIntegrationByParts Cvs.L2a.FarFarBound Cvs.L2a.ChebyshevRampBound

namespace Cvs.L2a.RampTopQuadratic

/-- On `[3/2, 2]`, `1 − wF(x) = sin²(π(2 − x))`. -/
theorem one_sub_wF_eq {x : ℝ} (hx : x ∈ Icc (3 / 2 : ℝ) 2) :
    1 - wF x = Real.sin (π * (2 - x)) ^ 2 := by
  rw [wF_eq_on hx, ← Real.cos_pi_div_two_sub (π * (2 - x)), show π / 2 - π * (2 - x) = π * x - 3 * π / 2 by ring]
  linarith [Real.sin_sq_add_cos_sq (π * x - 3 * π / 2)]

/-- **The quadratic vanishing at `2`**: `1 − wF(x) ≤ π²(2 − x)²` for every real `x`. -/
theorem one_sub_wF_le (x : ℝ) : 1 - wF x ≤ π ^ 2 * (2 - x) ^ 2 := by
  rcases le_or_gt x (3 / 2) with h1 | h1
  · rw [wF_eq_zero_of_le h1]
    have : (3 / 2 : ℝ) ≤ π * (2 - x) := by nlinarith [pi_gt_three]
    nlinarith
  rcases le_or_gt 2 x with h2 | h2
  · rw [(wF_of_two_le h2).1, sub_self]; positivity
  rw [one_sub_wF_eq ⟨h1.le, h2.le⟩, ← mul_pow]
  have h := Real.abs_sin_le_abs (x := π * (2 - x))
  rw [← sq_abs, ← sq_abs (π * (2 - x))]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

end Cvs.L2a.RampTopQuadratic

end
