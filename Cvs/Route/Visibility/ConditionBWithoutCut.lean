import Mathlib
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Condition (B) without a cut

Condition (B) depends on the AL-R constant `C₁` only through its limit, so it is `CEBound`:
`C₀∞·c_E^C ≤ κ < 2` eventually. Theorem A bounds `c_E^C` by the layer sum `Σ_k δ_k/F_k`, and once (EF′) holds at
one cut `T₁` the layer sum is bounded iff its part above `T₁` is, so the cut drops out. Both (WF′) and (WF₂) at
`T₁` bound that part, and so does a floor above `μ*C₀∞/2` at any rung `k(x)` whose deep remainder vanishes.
-/

noncomputable section

open Real Set Matrix Finset Filter Topology

namespace Cvs.Route.Visibility.ConditionBWithoutCut
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram mu muInc levT)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (cE floorC C0 C0inf muStar CondB WFprime EFprime)

/-! ### (B) is a bound on `c_E^C` alone -/

/-- **`CEBound`**: eventually `C₀∞·c_E^C ≤ κ` for some `κ < 2`. -/
def CEBound (Wt : ℝ) : Prop := ∃ κ < 2, ∀ᶠ x : ℕ in atTop, C0inf Wt * cE x ≤ κ

/-! ### The layer sum -/

/-! ### (WF′) and (WF₂) bound the part above the cut -/

/-! ### A floor at any rung whose deep remainder vanishes -/

end Cvs.Route.Visibility.ConditionBWithoutCut

end
