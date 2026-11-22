import Mathlib
import Cvs.Prolate.Gram.DirichletNodeCountPotFloor
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.Gram.TwoCutLayerBound
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.VisibilityAliasPlungeDischarge
import Cvs.Route.Visibility.VisibilityCentralSquareCut
import Cvs.Route.Visibility.VisibilityFullTwistPotential
import Cvs.Route.Visibility.VisibilityRightEdgeLaw
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV after wave 15

The discrete potential of Cvs.Prolate.Gram.DirichletNodeCountPotFloor in place of `PotFloor`, central-square exclusion at the cut of Cvs.Route.Visibility.VisibilityCentralSquareCut in place of
`CentralSquareFloor`, and the right-edge law with both edge values of Cvs.Prolate.Mellin.RungWindowLawRightEdge as the only window input.
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

namespace Cvs.Route.Visibility.VisibilityDiscretePotentialCut
open Cvs.ZeroCounting

/-- (WF₂) at `W̃ = 57/60` from central-square exclusion at a cut `T₀ < 1` below the threshold and the band floor. -/
theorem wfTwo_of_cut_band {T₀ ε : ℝ} (hT₀ : T₀ < 1) (hlt : ε < √2 * (1 / 2 - muStar * C0inf (57 / 60) / 2))
    (hCS : Cvs.Route.Visibility.VisibilityCentralSquareCut.CentralSquareCut T₀ ε) (hBF : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor) : Cvs.Prolate.Gram.TwoCutLayerBound.WFtwo (57 / 60) T₀ := by
  have hθ : 0 < √2 * (1 / 2 - muStar * C0inf (57 / 60) / 2) := by linarith [Cvs.Route.Visibility.VisibilityFullTwistPotential.twistThreshold_57_60_gt]
  obtain ⟨h1, h2, h3, h4⟩ := Cvs.Route.Visibility.VisibilityCentralSquareCut.split_threshold hθ hlt
  exact Cvs.Route.Visibility.VisibilityFullTwistPotential.wfTwo_of_centralSquare h3 h4
    (Cvs.Route.Visibility.VisibilityCentralSquareCut.centralSquareFloor_of_cut_pot_band hT₀ h2 Cvs.Prolate.Gram.DirichletNodeCountPotFloor.potFloor hBF (hCS.mono h1))

/-- hV from central-square exclusion at a cut `T₀ < 1` below the threshold, the band floor, KRD, `EdgeLawSum` and
Carlson. -/
theorem hV_wave15 {T₀ ε : ℝ} (hT₀ : T₀ < 1) (hlt : ε < √2 * (1 / 2 - muStar * C0inf (57 / 60) / 2))
    (hCS : Cvs.Route.Visibility.VisibilityCentralSquareCut.CentralSquareCut T₀ ε) (hBF : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor) (hK : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.KRDCount)
    (hB : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum) (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  Cvs.Route.Visibility.VisibilityAliasPlungeDischarge.hV_wave13 hT₀ (wfTwo_of_cut_band hT₀ hlt hCS hBF) Cvs.Prolate.Gram.DirichletNodeCountPotFloor.deepCellFloor hBF hK
    (Cvs.Route.Visibility.VisibilityRightEdgeLaw.winInput_of_edgeLawSum hB) hCarl

end Cvs.Route.Visibility.VisibilityDiscretePotentialCut

end
