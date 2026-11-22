import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The gain at index 1 never enters the resonant constant

For `k ≥ 2` the tail fraction `τ_k` of Cvs.L2a.RungSpanFromPlateau reads the gain sequence only at the indices `km′ ≥ 2`, so two gain
sequences that agree from 2 on give the same `τ_k`; and the trivial-gain hypothesis at `j = 1` holds with
`δ₁ = 1 − T/(Σ + T)` for any mode mass `Σ ≥ 0` and tail mass `T > 0`, so it costs nothing in the constant.
-/

namespace Cvs.L2a.IndexOneGainFree

open Finset

/-- **The trivial gain at `j = 1` is free**: `(1 − δ₁)Σ ≤ T` with `δ₁ = 1 − T/(Σ + T) < 1`. -/
theorem free_gain {S T : ℝ} (hS : 0 ≤ S) (hT : 0 < T) :
    1 - T / (S + T) < 1 ∧ (1 - (1 - T / (S + T))) * S ≤ T := by
  have hST : 0 < S + T := by linarith
  refine ⟨by have : 0 < T / (S + T) := div_pos hT hST; linarith, ?_⟩
  rw [sub_sub_cancel, div_mul_eq_mul_div, div_le_iff₀ hST]
  nlinarith

end Cvs.L2a.IndexOneGainFree
