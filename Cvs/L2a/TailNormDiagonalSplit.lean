import Mathlib
import Cvs.L2a.AdmixtureNegligibleModes
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailConvergence

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail norm splits into the mode diagonal and the pair off-diagonal

`∫_{θ>1} F_X² = Σ_{M<⌊X⌋} (1/(M+1))∫_{M+1}^X Φ² + Σ_{a≠n} ∫_1^{X/max(a,n)} Φ(aθ)Φ(nθ)` for `Φ` continuous on
`[1, X]`; a weighted diagonal `Σ_{M<⌊X⌋} v_M ∫_{M+1}^X Φ²` tends to `Σ_M v_M ∫_{M+1}^∞ Φ²` (Tannery); so for
`Φ = psi c g` the off-diagonal tends to `N_∞ − Σ_M T(M)/M`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.L2a.TailNormDiagonalSplit
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.PositionTruncatedTail (posTail pairI)
open Cvs.L2a.AdmixtureNegligibleModes (modeSum wInv)

/-! ### The weighted diagonal converges -/

/-! ### The cosine transforms -/

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-- `|psi c g w| ≤ B_G/w` on `w ≥ 1`, with `B_G` from the `C²` data. -/
theorem exists_abs_psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) : ∃ B, ∀ w, 1 ≤ w → |psi c g w| ≤ B / w :=
  ⟨_, fun _ hw => Cvs.L2a.FullTailArchChannel.abs_psi_le_BG hg hg₁ hg₂c hc hw⟩

end Cvs.L2a.TailNormDiagonalSplit
