import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tilt and the frame-free pole

For `1 ≤ X`, `Φ` continuous on `[1, X]` and `F = posTail Φ X` of Cvs.L2a.PositionTruncatedTail, the pole product is bounded below by the
tail mass: `-((X - 2 log X - 1/X)/2 · ∫_{(1,∞)} F²) ≤ 2 (∫ F)(∫ F/θ)`, from `2AB ≥ -(A-B)²/2`, the Cvs.WeilForm.OddPoleTermBound
Cauchy–Schwarz on `[1, X]` for the tilt `∫ F (1 - 1/θ)`, and `∫_1^X (1 - 1/θ)² = X - 2 log X - 1/X`.
-/

namespace Cvs.L2a.TiltFrameFreePole

open Real Set MeasureTheory

/-- The product `2AB` is at least `-(A - B)²/2`. -/
theorem neg_sq_sub_le (A B : ℝ) : -((A - B) ^ 2 / 2) ≤ 2 * A * B := by
  nlinarith [sq_nonneg (A + B)]

end Cvs.L2a.TiltFrameFreePole
