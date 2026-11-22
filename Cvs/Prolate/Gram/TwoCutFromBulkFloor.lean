import Mathlib
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# (WF₂) from a bulk floor and a floor at the plunge cut

The plunge cut of the dial `m < ½` is the first rung `k_p ≥ k₀` with `μ_{k_p} > m`; it exists because `μ_t ≥ ½`,
and the increments below it sum to at most `m`. So (WF₂) follows from a bulk floor `φ₀` at `k₀` and a floor `φ_p`
at `k_p` with `C₀∞(m/φ₀ + μ*/φ_p) < 2`. Both floors follow from (WF′). With `φ_p = μ*C₀∞/2 + ε` the bulk floor only
has to be positive: the dial `m` absorbs any `φ₀ > 0`.
-/

noncomputable section

open Real Set Matrix Finset Filter

namespace Cvs.Prolate.Gram.TwoCutFromBulkFloor
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (mu muInc levT lam lamTop)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (floorC C0inf muStar WFprime)

/-! ### The weights at the top and the floors along the layers -/

/-! ### The plunge cut -/

/-! ### The two floors -/

/-- **Bulk floor** `φ₀` at the cut `T₀`: eventually the first rung `k₀` of `A(T₀)` exists and `F_{k₀} ≥ φ₀`. -/
def BulkFloor (T₀ φ₀ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧ φ₀ ≤ floorC x k₀

end Cvs.Prolate.Gram.TwoCutFromBulkFloor
