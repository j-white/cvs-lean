import Mathlib
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.OneZeroSectorBottoms
import Cvs.StepA.SectorGramBoxTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One off-line zero alone: its two sector bottoms trade places infinitely often
For `Re z ≠ 0 ≠ Im z`, `lamO L z < lamE L z` for arbitrarily large `L`, and `lamE L z < lamO L z` for
arbitrarily large `L`. For `Re z ≠ 0`, `Im z < 0` and `L ≥ 2/(|z| + Im z)`: `4|∫ ue ve| ≤ κ (Σ_e + Σ_o)`
with `κ = (|z| − Im z)/(2|z|) < 1`, so `0 ≤ ρ ≤ K = (√((1 − κ²)/2))⁻¹`, and `lamO − lamE` is
`−e^{−(Im z) L} sin(xL − arg z)/(4|z|)` plus a remainder of size at most `K/(2|Re z|) + 1/(4|z|)`.
-/

noncomputable section

open Real Filter Topology Asymptotics

namespace Cvs.StepA.OffLineZeroTrade
open Cvs.ZeroCounting

open Cvs.StepA.OneZeroParitySectors (ue ve uo vo)
open Cvs.StepA.OneZeroSectorBottoms (lamE lamO sigE sigO)

/-! ### The Gram data, bounded -/

/-- The two traces add up to `∫ cosh 2yt`. -/
theorem sigE_add_sigO (L : ℝ) (z : ℂ) :
    sigE L z + sigO L z = ∫ t in -(L / 2)..L / 2, cosh (2 * z.im * t) := by
  unfold sigE sigO
  rw [Cvs.StepA.SectorGramBoxTransform.gram_even_add, Cvs.StepA.SectorGramBoxTransform.gram_odd_add]
  ring

/-! ### One zero with `Im z < 0` -/

/-! ### Every nonreal zero off the line -/

end Cvs.StepA.OffLineZeroTrade
