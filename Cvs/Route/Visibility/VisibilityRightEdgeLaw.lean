import Mathlib
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.WindowLogEnergyCellFloor

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV with the right-edge law as the only window input

Cvs.Prolate.Mellin.RungWindowLawRightEdge gives `WinTailProfile (1/4)` from `EdgeLawSum` (implied by `EdgeLaw`) alone, which is the second alternative
of the window input of Cvs.Route.Visibility.VisibilityAliasPlungeDischarge; the other inputs are those of Cvs.Route.Visibility.VisibilityFullTwistPotential.
-/

noncomputable section
open Real Filter
open Cvs.ZeroCounting
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0inf muStar)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.VisibilityRightEdgeLaw
open Cvs.ZeroCounting

/-- **The window input from the right-edge law with the two edge values**. -/
theorem winInput_of_edgeLawSum (hB : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum) :
    (∃ ν < 1, Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg ν) ∨ ∃ η' ≥ 0, Cvs.Route.Visibility.WindowLogEnergyCellFloor.WinTailProfile η' :=
  Or.inr ⟨1 / 4, by norm_num, Cvs.Prolate.Mellin.RungWindowLawRightEdge.winTailProfile_of_edgeLawSum hB⟩

end Cvs.Route.Visibility.VisibilityRightEdgeLaw

end
