import Mathlib
import Cvs.Prolate.Gram.BandCellMassFloor
import Cvs.Prolate.Gram.RobinQZeroFarExponent
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.VisibilityCentralSquareCut
import Cvs.Route.Visibility.VisibilityDiscretePotentialCut
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV after wave 16

`Cvs.Route.Visibility.VisibilityDiscretePotentialCut.hV_wave15` with the band floor from Theorem Q₀ on positions at the far exponent `K = 1`
(`Cvs.Prolate.Gram.RobinQZeroFarExponent.robinQ0_of_pos'`), whose far node rate is `FarRobinRate`'s `farRate`.
-/

noncomputable section

open Real Filter
open Cvs.ZeroCounting
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0inf muStar)

namespace Cvs.Route.Visibility.VisibilityRobinFarExponent
open Cvs.ZeroCounting

/-- The band floor from `PosQ0At 1`. -/
theorem bandFloor_of_posQ0At (hP : Cvs.Prolate.Gram.RobinQZeroFarExponent.PosQ0At 1) : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor :=
  Cvs.Prolate.Gram.BandCellMassFloor.bandFloor_of_robinQ0 (Cvs.Prolate.Gram.RobinQZeroFarExponent.robinQ0_of_pos' hP)

/-- hV from central-square exclusion at a cut `T₀ < 1` below the threshold, `PosQ0At 1`, KRD, `EdgeLawSum` and
Carlson. -/
theorem hV_wave16 {T₀ ε : ℝ} (hT₀ : T₀ < 1) (hlt : ε < √2 * (1 / 2 - muStar * C0inf (57 / 60) / 2))
    (hCS : Cvs.Route.Visibility.VisibilityCentralSquareCut.CentralSquareCut T₀ ε) (hP : Cvs.Prolate.Gram.RobinQZeroFarExponent.PosQ0At 1) (hK : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.KRDCount)
    (hB : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum) (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  Cvs.Route.Visibility.VisibilityDiscretePotentialCut.hV_wave15 hT₀ hlt hCS (bandFloor_of_posQ0At hP) hK hB hCarl

end Cvs.Route.Visibility.VisibilityRobinFarExponent

end
