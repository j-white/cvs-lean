import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band floor from the band central resolvent, and hV

`BandResolvent`: `B_jj = ⟨Qh_{4j}, (I − A)⁻¹Qh_{4j}⟩ ≤ x^ε` on the rungs with `T_j > ¾`; `BandHighpass`: those
`h_{4j}|_I` have highpass extensions of energy `≤ x^ε`. Either gives `Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor` through Cvs.Prolate.Gram.InverseCellGramResolvent, and then hV.
-/

noncomputable section

open Real Filter

namespace Cvs.Prolate.Gram.BandFloorFromResolvent


/-- `1 + K·x^{ε/2} ≤ x^ε` eventually in `x`, for `ε > 0` and `K ≥ 0`. -/
theorem eventually_add_mul_rpow_le {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    ∀ᶠ x : ℕ in atTop, 1 + K * (x : ℝ) ^ (ε / 2) ≤ (x : ℝ) ^ ε := by
  have ht : Tendsto (fun x : ℕ => (x : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (K + 1), eventually_ge_atTop 1] with x hy hx1
  have hx : (0 : ℝ) < x := by exact_mod_cast hx1
  have hsq : (x : ℝ) ^ ε = (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2) := by
    rw [← rpow_add hx]; ring_nf
  rw [hsq]
  nlinarith

end Cvs.Prolate.Gram.BandFloorFromResolvent

end
