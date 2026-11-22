import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The mass beyond `b` from the frame bound

`∫_b^{Mb} Φ² ≤ ∫_1^{Mb} Φ²` for `1 ≤ b ≤ Mb`, so a frame bound `∫_1^{Mb} Φ² ≤ K·N` gives the hypothesis of Cvs.L2a.PlateauAssemblyTrivialGain on
the mass beyond `b` with `ε₃ = K`: bounded in `c` whenever `K` is, which with a floor growing like `log c` leaves only
an explicit threshold on `c`.
-/

namespace Cvs.L2a.MassBeyondFrame

open Real Set MeasureTheory intervalIntegral

/-- **The mass beyond `b` from the frame bound.** -/
theorem beyond_le_frame {Φ : ℝ → ℝ} {b T K N : ℝ} (hb : 1 ≤ b) (hbT : b ≤ T)
    (hc : ContinuousOn Φ (Icc 1 T)) (hK : ∫ ξ in (1 : ℝ)..T, Φ ξ ^ 2 ≤ K * N) :
    ∫ ξ in b..T, Φ ξ ^ 2 ≤ K * N := by
  have h1T : (1 : ℝ) ≤ T := hb.trans hbT
  have hi1 : IntervalIntegrable (fun ξ => Φ ξ ^ 2) volume 1 b :=
    ((hc.mono (Icc_subset_Icc le_rfl hbT)).pow 2).intervalIntegrable_of_Icc hb
  have hi2 : IntervalIntegrable (fun ξ => Φ ξ ^ 2) volume b T :=
    ((hc.mono (Icc_subset_Icc hb le_rfl)).pow 2).intervalIntegrable_of_Icc hbT
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have h0 : 0 ≤ ∫ ξ in (1 : ℝ)..b, Φ ξ ^ 2 := intervalIntegral.integral_nonneg hb fun ξ _ => sq_nonneg _
  linarith

end Cvs.L2a.MassBeyondFrame
