import Mathlib
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.InfinitelyManyOffLattice
import Cvs.StepA.OddAboveDisplacement
import Cvs.StepA.OddBottomGapCriterion
import Cvs.StepA.PosDefOffLattice
import Cvs.StepA.StepACriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step (a) criterion with the count discharged

Under RH the off-lattice squared ordinates are infinite at every scale, so the count hypothesis leaves
positive definiteness, the odd bottom gap, step (a) below `2πN/L < 6.24`, and the criterion: RH holds iff
step (a) holds at all large scales and mode counts, given a strictly top quadruple when RH fails and,
under RH, an odd bottom eigenpair with `Ω_h` below every ordinate at all large scales and mode counts.
-/

noncomputable section

open Real

namespace Cvs.StepA.StepACountDischarged
open Cvs.ZeroCounting

open Cvs.StepA.OddBottomGapCriterion (OddBottomGap OddBottomBelow)

/-- **Under RH the window matrix is positive definite at every scale and mode count.** -/
theorem posDef_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (Cvs.Finite.ParitySectorDefect.MX L N).PosDef :=
  Cvs.StepA.PosDefOffLattice.posDef_of_RH hRH hL (Cvs.StepA.InfinitelyManyOffLattice.natCast_lt_encard_of_RH hRH hL N)

/-- **Under RH an odd bottom gap is an odd bottom eigenpair with `Ω_h` below every ordinate.** -/
theorem oddBottomGap_iff_oddBottomBelow_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L)
    (N : ℕ) : OddBottomGap L N ↔ OddBottomBelow L N :=
  ⟨fun h => ((Cvs.StepA.StepACriterion.oddBottomGap_iff_of_RH hRH hL).mp h).1,
    Cvs.StepA.OddBottomGapCriterion.oddBottomGap_of_RH_offLattice hRH hL
      (Cvs.StepA.InfinitelyManyOffLattice.natCast_lt_encard_of_RH hRH hL N)⟩

/-- **Under RH an odd bottom eigenpair with `Ω_h` below every ordinate gives step (a).** -/
theorem oddAbove_of_RH_of_oddBottomBelow (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) {N : ℕ}
    (h : OddBottomBelow L N) : Cvs.StepA.OddAboveDisplacement.OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N :=
  Cvs.StepA.OddBottomGapCriterion.oddAbove_of_oddBottomGap hRH hL
    ((oddBottomGap_iff_oddBottomBelow_of_RH hRH hL N).mpr h)

end Cvs.StepA.StepACountDischarged
